[%%import "../config.h"]

type code_loc = CL.Location.t
and param = code_loc list
and 'a arg = 'a se option list
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
  | App_V : 'a se * 'a arg -> 'a se (* possible values / force when arg = nil *)
  | App_P :
      'a se * 'a arg
      -> 'a se (* possible exn packets / force when arg = nil *)
  | Ctor : ctor * 'a se array -> 'a se (* construct / record field *)
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
let update_sc se1 se2 = Hashtbl.add insensitive_sc se1 se2

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

let list_rev_to_array l init =
  let len = List.length l in
  let arr = Array.make len init in
  let i = ref (len - 1) in
  let l = ref l in
  while !l != [] do
    match !l with
    | hd :: tl ->
      arr.(!i) <- hd;
      decr i;
      l := tl
    | _ -> assert false
  done;
  arr

let list_to_array l init =
  let len = List.length l in
  let arr = Array.make len init in
  let i = ref 0 in
  let l = ref l in
  while !l != [] do
    match !l with
    | hd :: tl ->
      arr.(!i) <- hd;
      incr i;
      l := tl
    | _ -> assert false
  done;
  arr

let se_of_int n = Const (CL.Asttypes.Const_int n)

let se_of_var x =
  let se_list =
    try SESet.elements (CL.Ident.Tbl.find var_to_se x)
    with err ->
      if !Common.Cli.debug then
        prerr_string
          ("Hey, I can't figure out : " ^ CL.Ident.unique_name x ^ "\n");
      raise err
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
    ( Ctor (Some (CL.Ident.name id, None), [|val_of_loc mod_loc|]),
      packet_of_loc mod_loc )
  | ({mb_id; mb_expr = {mod_loc}}
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    update_var mb_id (val_of_loc mod_loc);
    ( Ctor (Some (CL.Ident.name mb_id, None), [|val_of_loc mod_loc|]),
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
      | Some p -> solve_eq p (Fld (se, (constructor, se_of_int 0))))
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
    Ctor (Some (name, None), [|Or list|]) :: acc
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
  | Tstr_include {incl_mod = {mod_loc}; incl_type} ->
    let value = val_of_loc mod_loc in
    let exn = packet_of_loc mod_loc in
    (* rebind included values & modules *)
    let for_each_sig_item : CL.Types.signature_item -> unit = function
      | (Sig_value (x, _) | Sig_module (x, _, _))
      [@if ocaml_version < (4, 08, 0) || defined npm] ->
        update_var x (Fld (value, (Some (CL.Ident.name x, None), se_of_int 0)))
      | (Sig_value (x, _, _) | Sig_module (x, _, _, _, _))
      [@if ocaml_version >= (4, 08, 0) && not_defined npm] ->
        update_var x (Fld (value, (Some (CL.Ident.name x, None), se_of_int 0)))
      | _ -> ()
    in
    List.iter for_each_sig_item incl_type;
    (value, exn)
  | Tstr_primitive {val_id; val_val = {val_kind = Val_prim prim}} ->
    update_var val_id (Prim prim);
    (Prim prim, Bot)
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
  | ((Tmod_functor (Named (Some x, {loc}, _), me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    update_var x (Var (Val (Expr_var [loc])));
    (Fn ([loc], [Expr me.mod_loc]), Bot)
  | (Tmod_functor (Named (None, _, _), me) | Tmod_functor (Unit, me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm] ->
    (Fn ([CL.Location.none], [Expr me.mod_loc]), Bot)
  | ((Tmod_functor (x, {loc}, _, me))
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    update_var x (Var (Val (Expr_var [loc])));
    (Fn ([loc], [Expr me.mod_loc]), Bot)
  | Tmod_ident (x, {loc}) ->
    update_to_be loc x;
    (val_of_loc loc, packet_of_loc loc)
  | Tmod_structure structure -> se_of_struct structure
  | Tmod_apply (func, arg, _) ->
    ( App_V (val_of_loc func.mod_loc, [Some (val_of_loc arg.mod_loc)]),
      App_P (val_of_loc func.mod_loc, [Some (val_of_loc arg.mod_loc)]) )
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
      | None ->
        Ctor (constructor, [||])
        (* give up on being consistent with the actual mem repr *)
      | Some p ->
        let sub = solve_eq p (Fld (se, (constructor, se_of_int 0))) in
        Ctor (constructor, [|sub|]))
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
    Ctor (constructor, list_rev_to_array !args Bot)
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
    Ctor (None, list_rev_to_array !args Bot)
  in
  let val_list list =
    List.map (fun e -> val_of_loc e.CL.Typedtree.exp_loc) list
  in
  let exn_list list =
    List.map (fun e -> packet_of_loc e.CL.Typedtree.exp_loc) list
  in
  match expr.exp_desc with
  | Texp_function {cases} ->
    let value_pg, body = List.split (List.map extract cases) in
    let value_p, _ = List.split value_pg in
    let param = List.map (fun p -> p.CL.Typedtree.pat_loc) value_p in
    let arg = Var (Val (Expr_var param)) in
    List.fold_left solve_param arg value_pg |> ignore;
    (Fn (param, List.map (fun e -> Expr e.CL.Typedtree.exp_loc) body), Bot)
  | ((Texp_match (exp, cases, exn_cases, _))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let value_pg, value_body = List.split (List.map extract cases) in
    let exn_pg, exn_body = List.split (List.map extract exn_cases) in
    let val_exp = val_of_loc exp.exp_loc in
    let exn_exp = packet_of_loc exp.exp_loc in
    let () = List.fold_left solve_param val_exp value_pg |> ignore in
    let uncaught_exn = List.fold_left solve_param exn_exp exn_pg in
    let values = val_list (value_body @ exn_body) in
    let exns = exn_list (value_body @ exn_body) in
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
    let values = val_list body in
    let exns = exn_list body in
    (Or values, Or (uncaught_exn :: exns))
  | Texp_try (exp, cases) ->
    let exn_pg, body = List.split (List.map extract cases) in
    let uncaught_exn =
      List.fold_left solve_param (packet_of_loc exp.exp_loc) exn_pg
    in
    let values = val_list body in
    let exns = exn_list body in
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
      match o with Some e -> Some (val_of_loc e.exp_loc) | None -> None
    in
    let acc_packet acc (_, (o : CL.Typedtree.expression option)) =
      match o with Some e -> packet_of_loc e.exp_loc :: acc | None -> acc
    in
    let fn = val_of_loc e.exp_loc in
    let exn_fn = packet_of_loc e.exp_loc in
    let exn_args = List.fold_left acc_packet [] args in
    let args = List.map for_each_arg args in
    (App_V (fn, args), Or (App_P (fn, args) :: exn_fn :: exn_args))
  | Texp_tuple list ->
    let values = list_to_array (val_list list) Bot in
    let exns = exn_list list in
    (Ctor (None, values), Or exns)
  | Texp_construct (_, {cstr_name; cstr_loc}, list) ->
    let values = list_to_array (val_list list) Bot in
    let exns = exn_list list in
    (Ctor (Some (cstr_name, Some cstr_loc), values), Or exns)
  | Texp_record {fields; extended_expression} ->
    let plus_alpha = new_memory () in
    let for_each_field
        ( (l : CL.Types.label_description),
          (def : CL.Typedtree.record_label_definition) ) =
      let i = l.lbl_pos in
      let kept =
        match extended_expression with
        | Some e -> Fld (val_of_loc e.exp_loc, (None, se_of_int i))
        | _ -> Bot
      in
      let ith_field = Fld (plus_alpha, (None, se_of_int i)) in
      (match def with
      | Kept _ -> update_sc ith_field kept
      | Overridden (_, e) -> update_sc ith_field (val_of_loc e.exp_loc));
      ith_field
    in
    let acc_exns acc (_, (def : CL.Typedtree.record_label_definition)) =
      match def with
      | Overridden (_, e) -> packet_of_loc e.exp_loc :: acc
      | _ -> acc
    in
    let exns = Array.fold_left acc_exns [] fields in
    let exns =
      match extended_expression with
      | Some e -> packet_of_loc e.exp_loc :: exns
      | _ -> exns
    in
    (Ctor (None, Array.map for_each_field fields), Or exns)
  | Texp_field (e, _, lbl) ->
    let i = lbl.lbl_pos in
    (Fld (val_of_loc e.exp_loc, (None, se_of_int i)), packet_of_loc e.exp_loc)
  | Texp_variant (lbl, o) -> (
    match o with
    | Some e ->
      ( Ctor (Some (lbl, None), [|val_of_loc e.exp_loc|]),
        packet_of_loc e.exp_loc )
    | None -> (Ctor (Some (lbl, None), [||]), Bot))
  | Texp_setfield (e1, _, lbl, e2) ->
    let val1 = val_of_loc e1.exp_loc in
    let val2 = val_of_loc e2.exp_loc in
    let exn1 = packet_of_loc e1.exp_loc in
    let exn2 = packet_of_loc e2.exp_loc in
    update_sc (Fld (val1, (None, se_of_int lbl.lbl_pos))) val2;
    (Bot, Or [exn1; exn2])
  | Texp_array list ->
    let plus_alpha = new_memory () in
    let arr = list_to_array list expr in
    let for_each_expr_val i (expr : CL.Typedtree.expression) =
      let ith_field = Fld (plus_alpha, (None, se_of_int i)) in
      let kept = val_of_loc expr.exp_loc in
      update_sc ith_field kept;
      ith_field
    in
    let for_each_expr_exn (expr : CL.Typedtree.expression) =
      packet_of_loc expr.exp_loc
    in
    ( Ctor (None, Array.mapi for_each_expr_val arr),
      Or (List.map for_each_expr_exn list) )
  | Texp_ifthenelse (pred, if_true, Some if_false) ->
    let val1 = val_of_loc if_true.exp_loc in
    let val2 = val_of_loc if_false.exp_loc in
    let exn1 = packet_of_loc pred.exp_loc in
    let exn2 = packet_of_loc pred.exp_loc in
    let exn3 = packet_of_loc if_false.exp_loc in
    (Or [val1; val2], Or [exn1; exn2; exn3])
  | Texp_ifthenelse ({exp_loc = pred_loc}, {exp_loc = true_loc}, None) ->
    (val_of_loc true_loc, Or [packet_of_loc pred_loc; packet_of_loc true_loc])
  | Texp_sequence ({exp_loc = l1}, {exp_loc = l2}) ->
    (val_of_loc l2, Or [packet_of_loc l1; packet_of_loc l2])
  | Texp_while ({exp_loc = pred_loc}, {exp_loc = body_loc}) ->
    (Bot, Or [packet_of_loc pred_loc; packet_of_loc body_loc])
  | Texp_for
      ( i,
        {ppat_loc},
        {exp_loc = start_loc},
        {exp_loc = finish_loc},
        direction,
        {exp_loc = body_loc} ) ->
    let val_i = val_of_loc ppat_loc in
    let val_start = val_of_loc start_loc in
    let exn_start = packet_of_loc start_loc in
    let exn_finish = packet_of_loc finish_loc in
    let exn_body = packet_of_loc body_loc in
    let update_op =
      match direction with Upto -> INT ADD | Downto -> INT SUB
    in
    update_var i val_i;
    update_sc val_i (Union (val_start, Arith (update_op, [val_i; se_of_int 1])));
    (Bot, Or [exn_start; exn_finish; exn_body])
  | ((Texp_letmodule (x, {loc}, {mod_loc}, {exp_loc}))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let val_x = val_of_loc loc in
    let val_m = val_of_loc mod_loc in
    let val_e = val_of_loc exp_loc in
    let exn_m = packet_of_loc mod_loc in
    let exn_e = packet_of_loc exp_loc in
    update_var x val_x;
    update_sc val_x val_m;
    (val_e, Or [exn_m; exn_e])
  | ((Texp_letmodule (x, {loc}, _, {mod_loc}, {exp_loc}))
  [@if
    ocaml_version >= (4, 08, 0) && ocaml_version < (4, 10, 0) && not_defined npm])
    ->
    let val_x = val_of_loc loc in
    let val_m = val_of_loc mod_loc in
    let val_e = val_of_loc exp_loc in
    let exn_m = packet_of_loc mod_loc in
    let exn_e = packet_of_loc exp_loc in
    update_var x val_x;
    update_sc val_x val_m;
    (val_e, Or [exn_m; exn_e])
  | ((Texp_letmodule (Some x, {loc}, _, {mod_loc}, {exp_loc}))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let val_x = val_of_loc loc in
    let val_m = val_of_loc mod_loc in
    let val_e = val_of_loc exp_loc in
    let exn_m = packet_of_loc mod_loc in
    let exn_e = packet_of_loc exp_loc in
    update_var x val_x;
    update_sc val_x val_m;
    (val_e, Or [exn_m; exn_e])
  | ((Texp_letmodule (None, _, _, {mod_loc}, {exp_loc}))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let val_e = val_of_loc exp_loc in
    let exn_m = packet_of_loc mod_loc in
    let exn_e = packet_of_loc exp_loc in
    (val_e, Or [exn_m; exn_e])
  | Texp_letexception (_, {exp_loc}) ->
    (val_of_loc exp_loc, packet_of_loc exp_loc)
  | Texp_assert {exp_loc} ->
    (* How to express Assert_failure... *)
    (Bot, packet_of_loc exp_loc)
  | Texp_lazy {exp_loc} -> (Fn ([], [Expr exp_loc]), Bot)
  | Texp_pack {mod_loc} -> (val_of_loc mod_loc, packet_of_loc mod_loc)
  | ((Texp_letop {let_; ands; body})
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let let_path = let_.bop_op_path in
    let letop = val_of_loc let_.bop_op_name.loc in
    let bound =
      (val_of_loc let_.bop_exp.exp_loc, [packet_of_loc let_.bop_exp.exp_loc])
    in
    let for_each_and (acc_val, acc_exn_list) (andop : CL.Typedtree.binding_op) =
      let and_path = andop.bop_op_path in
      let and_val = val_of_loc andop.bop_op_name.loc in
      let bound_val = val_of_loc andop.bop_exp.exp_loc in
      let exn = packet_of_loc andop.bop_exp.exp_loc in
      let updated_val = App_V (and_val, [Some acc_val; Some bound_val]) in
      update_to_be andop.bop_op_name.loc and_path;
      (updated_val, exn :: acc_exn_list)
    in
    let bound_expr, exns = List.fold_left for_each_and bound ands in
    let body_fn = Fn ([body.c_lhs.pat_loc], [Expr body.c_rhs.exp_loc]) in
    let value = App_V (letop, [Some bound_expr; Some body_fn]) in
    let exn = App_P (letop, [Some bound_expr; Some body_fn]) in
    solve_eq body.c_lhs (Var (Val (Expr_var [body.c_lhs.pat_loc]))) |> ignore;
    update_to_be let_.bop_op_name.loc let_path;
    (value, Or (exn :: exns))
  | ((Texp_open (_, {exp_loc}))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    (val_of_loc exp_loc, packet_of_loc exp_loc)
  | _ -> (Bot, Bot)

(* expr, module_binding, module_expr, structure, structure_item, value_binding, value_bindings *)
(* se_of_something returns the set expressions corresponding to the location of "something" *)
(* tast_mapper connects val/exns returned by se_of_something with the code_loc of the AST node *)
(* var_to_se) correlates ident to se set_constraints) correlates location to se *)
(* after all cmt files are processed, lookup to_be_resolved to resolve Path.t. *)
