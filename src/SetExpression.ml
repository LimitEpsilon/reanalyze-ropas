[%%import "../config.h"]

type param = CL.Typedtree.pattern list
and arg = code_loc expr option list
and code_loc = CL.Location.t
and _ expr = Expr_var : param -> param expr | Expr : code_loc -> code_loc expr

and _ tagged_expr =
  | Val : 'a expr -> 'a tagged_expr
  | Packet : 'a expr -> 'a tagged_expr

and env = Env_var | Env of (param * code_loc tagged_expr) list

(* construct : Types.cstr_name, Some Types.cstr_loc *)
(* variant : Asttypes.label *)
and ctor = (string * code_loc option) option

(* construct : need to know arity *)
(* record : translate field name to position(int, starts from 0) *)
and 'a fld = ctor * 'a se

(* CL.Types.value_description.value_kind | Val_prim of {prim_name : string ;} *)
and arith =
  | ADD
  | SUB
  | DIV
  | MUL
  | NEG
  | ABS (* absolute value *)
  | MOD
  | AND
  | OR
  | NOT
  | XOR
  | LSL (* <<, logical *)
  | LSR (* >>, logical *)
  | ASR (* >>, arithmetic sign extension *)
  | SUCC (* ++x *)
  | PRED (* --x *)

and rel =
  | EQ (* == *)
  | NE (* != *)
  | LT (* < *)
  | LE (* <= *)
  | GT (* > *)
  | GE (* >= *)

and arithop =
  | INT of arith
  | INT32 of arith
  | INT64 of arith
  | FLOAT of arith
  | NATURALINT of arith

and relop = GEN of rel

(* set expression type *)
and _ se =
  | Bot : _ se (* empty set *)
  | Top : _ se (* _ *)
  | Const : CL.Asttypes.constant -> _ se
  | Mem : int -> _ se (* memory location, +\alpha to constructors *)
  | Prim :
      CL.Primitive.description
      -> _ se (* primitives, later converted to arith/rel/fld/mem *)
  | Fn : param * code_loc expr list -> unit se (* context-insensitive *)
  | Closure :
      param * code_loc expr list * env
      -> env se (* lambda (p->e)+ / lazy when param = nil *)
  | Var : _ tagged_expr -> unit se (* set variable, context-insensitive *)
  | Var_sigma : code_loc tagged_expr * env -> env se (* set variable *)
  | App_V : 'a se * arg -> 'a se (* possible values / force when arg = nil *)
  | App_P :
      'a se * arg
      -> 'a se (* possible exn packets / force when arg = nil *)
  | Ctor : ctor * 'a se list -> 'a se (* construct / record field *)
  | Fld : 'a se * 'a fld -> 'a se (* field of a record / deconstruct *)
  | Arith : arithop * 'a se list -> 'a se (* arithmetic operators *)
  | Rel : relop * 'a se list -> 'a se (* relation operators *)
  | Union : 'a se * 'a se -> 'a se (* union *)
  | Inter : 'a se * 'a se -> 'a se (* intersection *)
  | Diff : 'a se * 'a se -> 'a se (* difference *)
  | Or : 'a se list -> 'a se (* A|B : A or B, but not both. *)
  | Cond : 'a se * 'a se -> 'a se (* conditional set expression *)

(* divide_by_zero : check denominator, if constant check if zero.          *)
(*                : if identifier look up in var_to_se to check if constant*)
(*                : if constant check if zero, else mark might_raise       *)
and rule =
  [ `APP
  | `FORCE
  | `IGNORE
  | `IDENTITY
  | `ARITH
  | `REL
  | `EXTERN
  | `FN
  | `VAR
  | `LET
  | `OP
  | `CON
  | `FIELD
  | `SETFIELD
  | `SEQ
  | `CASE
  | `HANDLE
  | `RAISE
  | `FOR
  | `WHILE ]

let address = ref 0

let new_memory () : 'a se =
  let mem = Mem !address in
  address := !address + 1;
  mem

module SE = struct
  type t = unit se

  let compare = compare
end

module SESet = Set.Make (SE)

let insensitive_sc : (unit se, unit se) Hashtbl.t = Hashtbl.create 256
let sensitive_sc : (env se, env se) Hashtbl.t = Hashtbl.create 256

type var_se_tbl = SESet.t CL.Ident.Tbl.t

let var_to_se : var_se_tbl = CL.Ident.Tbl.create 256

let update_var key data =
  let singleton = SESet.singleton data in
  if CL.Ident.Tbl.mem var_to_se key then (
    let original = CL.Ident.Tbl.find var_to_se key in
    CL.Ident.Tbl.remove var_to_se key;
    CL.Ident.Tbl.add var_to_se key (SESet.union original singleton))
  else CL.Ident.Tbl.add var_to_se key singleton

type to_be_resolved = (code_loc, CL.Path.t) Hashtbl.t

let to_be_resolved : to_be_resolved = Hashtbl.create 256
let update_to_be key data = Hashtbl.add to_be_resolved key data

let union_of_list l =
  let make_union acc se =
    match acc with
    | Bot -> se
    | _ -> ( match se with Bot -> acc | _ -> Union (se, acc))
  in
  List.fold_left make_union Bot l

let se_of_int n = Const (CL.Asttypes.Const_int n)

let se_of_var x =
  let se_list =
    try SESet.elements (CL.Ident.Tbl.find var_to_se x) with _ -> []
  in
  Or se_list

let val_of_loc loc = Var (Val (Expr loc))
let packet_of_loc loc = Var (Packet (Expr loc))

(** se_of_something returns (value_of_something, packet_of_something) *)

(** The "value" of a binding is the union of all the "constructs" that are tagged with the bound names *)
let se_of_mb (mb : CL.Typedtree.module_binding) =
  match mb with
  | ({mb_id = Some id; mb_expr = {mod_loc}}
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    update_var id (val_of_loc mod_loc);
    ( Ctor (Some (CL.Ident.name id, None), [val_of_loc mod_loc]),
      packet_of_loc mod_loc )
  | ({mb_id; mb_expr = {mod_loc}}
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    update_var mb_id (val_of_loc mod_loc);
    ( Ctor (Some (CL.Ident.name mb_id, None), [val_of_loc mod_loc]),
      packet_of_loc mod_loc )
  | {mb_expr = {mod_loc}} -> (Bot, packet_of_loc mod_loc)

let se_of_vb (vb : CL.Typedtree.value_binding) =
  let local_binding : (string, unit se list) Hashtbl.t = Hashtbl.create 10 in
  (* update the table *)
  let update_tbl key data =
    if Hashtbl.mem local_binding key then (
      let original = Hashtbl.find local_binding key in
      Hashtbl.remove local_binding key;
      Hashtbl.add local_binding key (data :: original))
    else Hashtbl.add local_binding key [data]
  in
  (* update the table while traversing the pattern *)
  let rec solve_eq (pat : CL.Typedtree.pattern) se =
    match pat.pat_desc with
    | Tpat_any | Tpat_constant _ -> ()
    | Tpat_var (x, _) ->
      update_var x se;
      update_tbl (CL.Ident.name x) se
    | Tpat_alias (p, a, _) ->
      update_var a se;
      update_tbl (CL.Ident.name a) se;
      solve_eq p se
    | Tpat_tuple list -> solve_ctor None se list
    | ((Tpat_construct (_, {cstr_name; cstr_loc}, list, _))
    [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
      solve_ctor (Some (cstr_name, Some cstr_loc)) se list
    | ((Tpat_construct (_, {cstr_name; cstr_loc}, list))
    [@if ocaml_version < (4, 13, 0) || defined npm]) ->
      solve_ctor (Some (cstr_name, Some cstr_loc)) se list
    | Tpat_variant (lbl, p_o, _) -> (
      let constructor = Some (lbl, None) in
      match p_o with
      | None -> ()
      | Some p -> solve_eq p (Fld (se, (constructor, se_of_int 1))))
    | Tpat_record (key_val_list, _) ->
      let list =
        List.map (fun (_, lbl, pat) -> (lbl.CL.Types.lbl_pos, pat)) key_val_list
      in
      solve_rec se list
    | Tpat_array list -> solve_ctor None se list
    | Tpat_lazy p -> solve_eq p (App_V (se, []))
    | Tpat_or (lhs, rhs, _) ->
      solve_eq lhs se;
      solve_eq rhs se
  and solve_ctor constructor se list =
    let l = ref list in
    let i = ref 0 in
    while !l != [] do
      (match !l with
      | hd :: tl ->
        solve_eq hd (Fld (se, (constructor, se_of_int !i)));
        l := tl
      | _ -> assert false);
      i := !i + 1
    done
  and solve_rec se list =
    let l = ref list in
    while !l != [] do
      match !l with
      | hd :: tl ->
        let i, p = hd in
        solve_eq p (Fld (se, (None, se_of_int i)));
        l := tl
      | _ -> assert false
    done
  in
  solve_eq vb.vb_pat (val_of_loc vb.vb_expr.exp_loc);
  let for_each_binding acc (name, list) =
    Ctor (Some (name, None), [Or list]) :: acc
  in
  let seq_of_bindings = Hashtbl.to_seq local_binding in
  let ctor_list = Seq.fold_left for_each_binding [] seq_of_bindings in
  (union_of_list ctor_list, packet_of_loc vb.vb_expr.exp_loc)

let se_of_struct_item (item : CL.Typedtree.structure_item) =
  let for_each_vb (vb : CL.Typedtree.value_binding) =
    (val_of_loc vb.vb_loc, packet_of_loc vb.vb_loc)
  in
  let for_each_mb (mb : CL.Typedtree.module_binding) =
    (val_of_loc mb.mb_loc, packet_of_loc mb.mb_loc)
  in
  match item.str_desc with
  | Tstr_eval (e, _) -> (Bot, packet_of_loc e.exp_loc)
  | Tstr_value (_, vbs) ->
    let v, p = List.split (List.map for_each_vb vbs) in
    (union_of_list v, Or p)
  | Tstr_module mb -> for_each_mb mb
  | Tstr_recmodule mbs ->
    let v, p = List.split (List.map for_each_mb mbs) in
    (union_of_list v, Or p)
  | Tstr_include {incl_mod = {mod_loc}} ->
    (val_of_loc mod_loc, packet_of_loc mod_loc)
  | _ -> (Bot, Bot)

(* a struct is a union of constructs *)
let se_of_struct (str : CL.Typedtree.structure) =
  let for_each_item (item : CL.Typedtree.structure_item) =
    (val_of_loc item.str_loc, packet_of_loc item.str_loc)
  in
  let v, p = List.split (List.map for_each_item str.str_items) in
  (union_of_list v, Or p)

let se_of_module_expr (m : CL.Typedtree.module_expr) =
  match m.mod_desc with
  | ((Tmod_functor (Named (Some x, {txt = Some s; loc}, _), me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_var (x, {txt = s; loc});
        pat_loc = loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    update_var x (Var (Val (Expr_var [pat])));
    (Fn ([pat], [Expr me.mod_loc]), Bot)
  | ((Tmod_functor (Named (Some x, {txt = None; loc}, _), me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_var (x, {txt = ""; loc});
        pat_loc = loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    update_var x (Var (Val (Expr_var [pat])));
    (Fn ([pat], [Expr me.mod_loc]), Bot)
  | (Tmod_functor (Named (None, _, _), me) | Tmod_functor (Unit, me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm] ->
    let loc = CL.Location.mknoloc () in
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_any;
        pat_loc = loc.loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    (Fn ([pat], [Expr me.mod_loc]), Bot)
  | ((Tmod_functor (x, loc, _, me))
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_var (x, loc);
        pat_loc = loc.loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    update_var x (Var (Val (Expr_var [pat])));
    (Fn ([pat], [Expr me.mod_loc]), Bot)
  | Tmod_ident (x, {loc}) ->
    update_to_be loc x;
    (val_of_loc loc, packet_of_loc loc)
  | Tmod_structure structure -> se_of_struct structure
  | Tmod_apply (func, arg, _) ->
    ( App_V (val_of_loc func.mod_loc, [Some (Expr arg.mod_loc)]),
      App_P (val_of_loc func.mod_loc, [Some (Expr arg.mod_loc)]) )
  | Tmod_constraint (m, _, _, _) ->
    (val_of_loc m.mod_loc, packet_of_loc m.mod_loc)
  | Tmod_unpack (e, _) -> (val_of_loc e.exp_loc, packet_of_loc e.exp_loc)

(** determine whether or not to shadow the following cases by checking the existence of a guard *)
let extract c =
  let lhs = c.CL.Typedtree.c_lhs in
  let guard = c.CL.Typedtree.c_guard in
  let rhs = c.CL.Typedtree.c_rhs in
  match guard with None -> ((lhs, false), rhs) | _ -> ((lhs, true), rhs)

let se_of_expr (expr : CL.Typedtree.expression) =
  (* solves p_i = acc, that is, p_1 = se; p_2 = se - p_1; ... *)
  let rec solve_param (acc : unit se) (pattern, guarded) =
    if guarded then (
      solve_eq pattern acc |> ignore;
      acc)
    else Diff (acc, solve_eq pattern acc)
  (* solves p = se and returns the set expression for p *)
  and solve_eq (p : CL.Typedtree.pattern) (se : unit se) : unit se =
    match p.pat_desc with
    | Tpat_any -> Top
    | Tpat_var (x, _) ->
      update_var x se;
      Top
    | Tpat_alias (p, a, _) ->
      update_var a se;
      solve_eq p se
    | Tpat_constant c -> Const c
    | Tpat_tuple list -> solve_ctor None se list
    | ((Tpat_construct (_, {cstr_name; cstr_loc}, list, _))
    [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
      solve_ctor (Some (cstr_name, Some cstr_loc)) se list
    | ((Tpat_construct (_, {cstr_name; cstr_loc}, list))
    [@if ocaml_version < (4, 13, 0) || defined npm]) ->
      solve_ctor (Some (cstr_name, Some cstr_loc)) se list
    | Tpat_variant (lbl, p_o, _) -> (
      let constructor = Some (lbl, None) in
      match p_o with
      | None -> Ctor (constructor, [Top]) (* hash of the variant name *)
      | Some p ->
        let sub = solve_eq p (Fld (se, (constructor, se_of_int 1))) in
        Ctor (constructor, [Top; sub]))
    | Tpat_record (key_val_list, _) ->
      let list =
        List.map (fun (_, lbl, pat) -> (lbl.CL.Types.lbl_pos, pat)) key_val_list
      in
      let lbl_all =
        match key_val_list with
        | (_, {CL.Types.lbl_all = l}, _) :: _ -> l
        | _ -> failwith "Tried to match a record type without any fields"
      in
      let len = Array.length lbl_all in
      solve_rec len se list
    | Tpat_array list -> solve_ctor None se list
    | Tpat_lazy p -> solve_eq p (App_V (se, []))
    | Tpat_or (lhs, rhs, _) -> Union (solve_eq lhs se, solve_eq rhs se)
  and solve_ctor constructor se list =
    let l = ref list in
    let args = ref [] in
    let i = ref 0 in
    while !l != [] do
      (match !l with
      | hd :: tl ->
        let ith_se = solve_eq hd (Fld (se, (constructor, se_of_int !i))) in
        args := ith_se :: !args;
        l := tl
      | _ -> assert false);
      i := !i + 1
    done;
    Ctor (constructor, List.rev !args)
  and solve_rec len se list =
    let l = ref list in
    let args = ref [] in
    let cursor = ref 0 in
    while !l != [] do
      match !l with
      | hd :: tl ->
        let i, p = hd in
        let ith_se = solve_eq p (Fld (se, (None, se_of_int i))) in
        while !cursor < i do
          args := Top :: !args;
          cursor := !cursor + 1
        done;
        args := ith_se :: !args;
        cursor := !cursor + 1;
        l := tl
      | _ -> assert false
    done;
    while !cursor < len do
      args := Top :: !args;
      cursor := !cursor + 1
    done;
    Ctor (None, List.rev !args)
  in
  match expr.exp_desc with
  | Texp_function {cases} ->
    let value_pg, body = List.split (List.map extract cases) in
    let value_p, _ = List.split value_pg in
    let arg = Var (Val (Expr_var value_p)) in
    List.fold_left solve_param arg value_pg |> ignore;
    (Fn (value_p, List.map (fun e -> Expr e.CL.Typedtree.exp_loc) body), Bot)
  | ((Texp_match (exp, cases, exn_cases, _))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let value_pg, value_body = List.split (List.map extract cases) in
    let exn_pg, exn_body = List.split (List.map extract exn_cases) in
    let val_exp = val_of_loc exp.exp_loc in
    let exn_exp = packet_of_loc exp.exp_loc in
    let () = List.fold_left solve_param val_exp value_pg |> ignore in
    let uncaught_exn = List.fold_left solve_param exn_exp exn_pg in
    let values =
      List.map
        (fun e -> val_of_loc e.CL.Typedtree.exp_loc)
        (value_body @ exn_body)
    in
    let exns =
      List.map
        (fun e -> packet_of_loc e.CL.Typedtree.exp_loc)
        (value_body @ exn_body)
    in
    (Or values, Or (uncaught_exn :: exns))
  | ((Texp_match (exp, cases, _))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let pg, body = List.split (List.map extract cases) in
    let p, g = List.split pg in
    let o = List.map CL.Typedtree.split_pattern p in
    let rec filter o g =
      match o with
      | (Some v, Some e) :: o' -> (
        match g with
        | b :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v :: v_p, b :: v_g, e :: e_p, b :: e_g)
        | _ -> assert false)
      | (Some v, None) :: o' -> (
        match g with
        | b :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v :: v_p, b :: v_g, e_p, e_g)
        | _ -> assert false)
      | (None, Some e) :: o' -> (
        match g with
        | b :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v_p, v_g, e :: e_p, b :: e_g)
        | _ -> assert false)
      | (None, None) :: o' -> (
        match g with
        | _ :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v_p, v_g, e_p, e_g)
        | _ -> assert false)
      | [] -> ([], [], [], [])
    in
    let value_p, value_g, exn_p, exn_g = filter o g in
    let value_pg = List.combine value_p value_g in
    let exn_pg = List.combine exn_p exn_g in
    let () =
      List.fold_left solve_param (val_of_loc exp.exp_loc) value_pg |> ignore
    in
    let uncaught_exn =
      List.fold_left solve_param (packet_of_loc exp.exp_loc) exn_pg
    in
    let values = List.map (fun e -> val_of_loc e.CL.Typedtree.exp_loc) body in
    let exns = List.map (fun e -> packet_of_loc e.CL.Typedtree.exp_loc) body in
    (Or values, Or (uncaught_exn :: exns))
  | Texp_try (exp, cases) ->
    let exn_pg, body = List.split (List.map extract cases) in
    let uncaught_exn =
      List.fold_left solve_param (packet_of_loc exp.exp_loc) exn_pg
    in
    let values = List.map (fun e -> val_of_loc e.CL.Typedtree.exp_loc) body in
    let exns = List.map (fun e -> packet_of_loc e.CL.Typedtree.exp_loc) body in
    (Or values, Or (uncaught_exn :: exns))
  | Texp_let (_, vbs, e) ->
    let exns = List.map (fun vb -> packet_of_loc vb.CL.Typedtree.vb_loc) vbs in
    (val_of_loc e.exp_loc, Or (packet_of_loc e.exp_loc :: exns))
  | Texp_ident (_, _, {val_kind = Val_prim prim}) -> (Prim prim, Bot)
  | Texp_ident (x, {loc}, _) ->
    update_to_be loc x;
    (val_of_loc loc, packet_of_loc loc)
  | Texp_constant c -> (Const c, Bot)
  | Texp_apply (e, args) ->
    let for_each_arg (_, (o : CL.Typedtree.expression option)) =
      match o with Some e -> Some (Expr e.exp_loc) | None -> None
    in
    let acc_packet acc (_, (o : CL.Typedtree.expression option)) =
      match o with Some e -> (packet_of_loc e.exp_loc) :: acc | None -> acc
    in
    let fn = val_of_loc e.exp_loc in
    let exn_args = List.fold_left acc_packet [] args in
    let args = List.map for_each_arg args in
    (App_V (fn, args), Or (App_P (fn, args) :: exn_args))
  | Texp_tuple list ->
    let val_list = List.map (fun e -> val_of_loc e.CL.Typedtree.exp_loc) list in
    let exn_list =
      List.map (fun e -> packet_of_loc e.CL.Typedtree.exp_loc) list
    in
    (Ctor (None, val_list), Or exn_list)
  | _ -> (Bot, Bot)

(* expr, module_binding, module_expr, structure, structure_item, value_binding, value_bindings *)
(* se_of_something returns the set expression corresponding to the location of "something" *)
(* something = expr, module_expr, structure *)
(* tast_mapper updates set constraints *)
(* var_to_se) correlates ident to se set_constraints) correlates location to se *)
(* after all cmt files are processed, lookup to_be_resolved to resolve Path.t. *)
