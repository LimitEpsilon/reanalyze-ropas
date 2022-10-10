[%%import "../config.h"]

type code_loc =
  | Expr_loc of CL.Typedtree.expression
  | Mod_loc of CL.Typedtree.module_expr
  | Bop_loc of CL.Types.value_description

and param = CL.Ident.t option (* use Texp_function's param *)
and arg = value se option list

and _ expr =
  | Expr_var : CL.Ident.t -> param expr
  | Expr : code_loc -> code_loc expr

and arr =
  | Static of int array
      (** statically allocated arrays such as records, variants, or tuples *)
  | Dynamic of int
      (** dynamically allocated array, decoded from the Prim set expression *)

and _ tagged_expr =
  | Val : 'a expr -> 'a tagged_expr
  | Packet : 'a expr -> 'a tagged_expr

and ctor = string option
(** variant : Some Types.cstr_name
    polymorphic variant : Some Asttypes.label
    tuple or record or array : None *)

and fld = ctor * int option
(** i-th field of a variant : (Some κ, Some i)
    i-th field of a tuple or record : (None, Some i)
    dynamic access through the Array.get primitive : (None, None) *)

and arith =
  | ADD
  | SUB
  | DIV
  | MUL
  | NEG
  | ABS  (** absolute value *)
  | MOD
  | AND
  | OR
  | NOT
  | XOR
  | LSL  (** <<, logical *)
  | LSR  (** >>, logical *)
  | ASR  (** >>, arithmetic sign extension *)
  | SUCC  (** ++x *)
  | PRED  (** --x *)

and rel =
  | EQ  (** == *)
  | NE  (** != *)
  | LT  (** < *)
  | LE  (** <= *)
  | GT  (** > *)
  | GE  (** >= *)

and arithop =
  | INT of arith
  | INT32 of arith
  | INT64 of arith
  | FLOAT of arith
  | NATURALINT of arith

and relop = GEN of rel
and pattern
(* phantom type for pattern screening *)

and value

(** set expression type *)
and _ se =
  | Top : _ se  (** _ *)
  | Const : CL.Asttypes.constant -> _ se
  | Prim : CL.Primitive.description -> value se
      (** primitives, later converted to arith/rel/fld/mem *)
  | Fn : param * code_loc expr list -> value se  (** lambda expression *)
  | Var : _ tagged_expr -> _ se  (** set variable *)
  | App_V : value se * arg -> value se
      (** possible values / force when arg = nil / prim_v when lhs is Prim *)
  | App_P : value se * arg -> value se
      (** possible exn packets / force when arg = nil / prim_p when lhs is Prim *)
  | Ctor : ctor * arr -> value se  (** One ADT to rule them all :D *)
  | Ctor_pat : ctor * pattern se array -> pattern se
      (** For pattern screening *)
  | Fld : value se * fld -> value se  (** field of a record / deconstruct *)
  | Arith : arithop * value se list -> value se  (** arithmetic operators *)
  | Rel : relop * value se list -> value se  (** relation operators *)
  | Diff : value se * pattern se -> value se  (** screening *)
  | Loc : int * pattern se option -> pattern se

(* divide_by_zero : check denominator, if constant check if zero.
                  : if identifier look up in var_to_se to check if constant
                  : if constant check if zero, else mark might_raise *)

let temp_variable_label = ref 0

let new_temp_var () =
  let temp = !temp_variable_label in
  let temp_id = CL.Ident.create_persistent ("__temp" ^ string_of_int temp) in
  incr temp_variable_label;
  Expr_var temp_id

let address = ref 0

let new_memory () =
  let mem = !address in
  incr address;
  mem

let new_array size =
  let arr = Array.make size () in
  Array.map new_memory arr

module SE = struct
  type t = value se

  let compare = compare
end

module SESet = Set.Make (SE)

let sc : (value se, SESet.t) Hashtbl.t = Hashtbl.create 256

let update_sc key data =
  let set = SESet.of_list data in
  if Hashtbl.mem sc key then (
    let original = Hashtbl.find sc key in
    Hashtbl.remove sc key;
    Hashtbl.add sc key (SESet.union original set))
  else Hashtbl.add sc key set

type var_se_tbl = (CL.Ident.t, SESet.t) Hashtbl.t

let var_to_se : var_se_tbl = Hashtbl.create 256

let update_var key data =
  let set = SESet.of_list data in
  if Hashtbl.mem var_to_se key then (
    let original = Hashtbl.find var_to_se key in
    Hashtbl.remove var_to_se key;
    Hashtbl.add var_to_se key (SESet.union original set))
  else Hashtbl.add var_to_se key set

type to_be_resolved = (code_loc, CL.Path.t) Hashtbl.t

let to_be_resolved : to_be_resolved = Hashtbl.create 256
let update_to_be key data = Hashtbl.add to_be_resolved key data
let mem : (int, SESet.t) Hashtbl.t = Hashtbl.create 256

let update_mem key data =
  let set = SESet.of_list data in
  if Hashtbl.mem mem key then (
    let original = Hashtbl.find mem key in
    Hashtbl.remove mem key;
    Hashtbl.add mem key (SESet.union original set))
  else Hashtbl.add mem key set

let list_to_array l =
  let len = List.length l in
  if len = 0 then [||]
  else
    let arr = Array.make len (List.hd l) in
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

let se_of_var x =
  let se_list =
    try SESet.elements (Hashtbl.find var_to_se x)
    with err ->
      if !Common.Cli.debug then
        prerr_string
          ("Hey, I can't figure out : " ^ CL.Ident.unique_name x ^ "\n");
      raise err
  in
  se_list

let loc_of_mod mod_expr = Mod_loc mod_expr
let expr_of_mod me = Expr (loc_of_mod me)
let val_of_mod me = Var (Val (expr_of_mod me))
let packet_of_mod me = Var (Packet (expr_of_mod me))
let loc_of_expr expr = Expr_loc expr
let expr_of_expr e = Expr (loc_of_expr e)
let val_of_expr e = Var (Val (expr_of_expr e))
let packet_of_expr e = Var (Packet (expr_of_expr e))

(** se_of_something returns (value_of_something, packet_of_something) *)

(** The "value" of a binding is the union of all the "constructs" that are tagged with the bound names *)
let se_of_mb (mb : CL.Typedtree.module_binding) =
  match mb with
  | ({mb_id = Some id; mb_expr}
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let mem = new_memory () in
    update_var id [val_of_mod mb_expr];
    update_mem mem [val_of_mod mb_expr];
    ([Ctor (Some (CL.Ident.name id), Static [|mem|])], [packet_of_mod mb_expr])
  | ({mb_id; mb_expr} [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    let mem = new_memory () in
    update_var mb_id [val_of_mod mb_expr];
    update_mem mem [val_of_mod mb_expr];
    ( [Ctor (Some (CL.Ident.name mb_id), Static [|mem|])],
      [packet_of_mod mb_expr] )
  | {mb_expr} -> ([], [packet_of_mod mb_expr])

let se_of_vb (vb : CL.Typedtree.value_binding) =
  let local_binding : (string, value se list) Hashtbl.t = Hashtbl.create 10 in
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
    (* Does not return its set expression, as it does not require screening *)
    match pat.pat_desc with
    | Tpat_any | Tpat_constant _ -> ()
    | Tpat_var (x, _) ->
      update_var x [se];
      update_tbl (CL.Ident.name x) se
    | Tpat_alias (p, a, _) ->
      update_var a [se];
      update_tbl (CL.Ident.name a) se;
      solve_eq p se
    | Tpat_tuple list -> solve_ctor None se list
    | ((Tpat_construct (_, {cstr_name}, list, _))
    [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
      solve_ctor (Some cstr_name) se list
    | ((Tpat_construct (_, {cstr_name}, list))
    [@if ocaml_version < (4, 13, 0) || defined npm]) ->
      solve_ctor (Some cstr_name) se list
    | Tpat_variant (lbl, p_o, _) -> (
      let constructor = Some lbl in
      match p_o with
      | None -> ()
      | Some p ->
        let temp = Var (Val (new_temp_var ())) in
        update_sc temp [Fld (se, (constructor, Some 0))];
        solve_eq p temp)
    | Tpat_record (key_val_list, _) ->
      let list =
        List.map (fun (_, lbl, pat) -> (lbl.CL.Types.lbl_pos, pat)) key_val_list
      in
      solve_rec se list
    | Tpat_array list -> solve_ctor None se list
    | Tpat_lazy p ->
      let temp = Var (Val (new_temp_var ())) in
      update_sc temp [App_V (se, [])];
      solve_eq p temp
    | Tpat_or (lhs, rhs, _) ->
      solve_eq lhs se;
      solve_eq rhs se
  and solve_ctor constructor se list =
    let l = ref list in
    let i = ref 0 in
    while !l != [] do
      (match !l with
      | hd :: tl ->
        let temp = Var (Val (new_temp_var ())) in
        update_sc temp [Fld (se, (constructor, Some !i))];
        solve_eq hd temp;
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
        let temp = Var (Val (new_temp_var ())) in
        update_sc temp [Fld (se, (None, Some i))];
        solve_eq p temp;
        l := tl
      | _ -> assert false
    done
  in
  solve_eq vb.vb_pat (val_of_expr vb.vb_expr);
  let for_each_binding acc (name, list) =
    (let mem = new_memory () in
     update_mem mem list;
     Ctor (Some name, Static [|mem|]))
    :: acc
  in
  let seq_of_bindings = Hashtbl.to_seq local_binding in
  let ctor_list = Seq.fold_left for_each_binding [] seq_of_bindings in
  (ctor_list, [packet_of_expr vb.vb_expr])

let se_of_struct_item (item : CL.Typedtree.structure_item) =
  match item.str_desc with
  | Tstr_eval (e, _) -> ([], [packet_of_expr e])
  | Tstr_value (_, vbs) ->
    let v, p = List.split (List.map se_of_vb vbs) in
    (List.flatten v, List.flatten p)
  | Tstr_module mb ->
    let v, p = se_of_mb mb in
    (v, p)
  | Tstr_recmodule mbs ->
    let v, p = List.split (List.map se_of_mb mbs) in
    (List.flatten v, List.flatten p)
  | Tstr_include {incl_mod; incl_type} ->
    let value = val_of_mod incl_mod in
    (* rebind included values & modules *)
    let for_each_sig_item : CL.Types.signature_item -> unit = function
      | (Sig_value (x, _) | Sig_module (x, _, _))
      [@if ocaml_version < (4, 08, 0) || defined npm] ->
        update_var x [Fld (value, (Some (CL.Ident.name x), Some 0))]
      | (Sig_value (x, _, _) | Sig_module (x, _, _, _, _))
      [@if ocaml_version >= (4, 08, 0) && not_defined npm] ->
        update_var x [Fld (value, (Some (CL.Ident.name x), Some 0))]
      | _ -> ()
    in
    List.iter for_each_sig_item incl_type;
    ([value], [])
  | _ -> ([], [])

(* a struct is a union of constructs *)
let se_of_struct (str : CL.Typedtree.structure) =
  let v, p = List.split (List.map se_of_struct_item str.str_items) in
  (List.flatten v, List.flatten p)

let se_of_module_expr (m : CL.Typedtree.module_expr) =
  match m.mod_desc with
  | ((Tmod_functor (Named (Some x, _, _), me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    update_var x [Var (Val (Expr_var x))];
    ([Fn (Some x, [expr_of_mod me])], [])
  | (Tmod_functor (Named (None, _, _), me) | Tmod_functor (Unit, me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm] ->
    ([Fn (None, [expr_of_mod me])], [])
  | ((Tmod_functor (x, _, _, me))
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    update_var x [Var (Val (Expr_var x))];
    ([Fn (Some x, [expr_of_mod me])], [])
  | Tmod_ident (x, _) ->
    update_to_be (loc_of_mod m) x;
    ([], [])
  | Tmod_structure structure -> se_of_struct structure
  | Tmod_apply (func, arg, _) ->
    ( [App_V (val_of_mod func, [Some (val_of_mod arg)])],
      [packet_of_mod func; packet_of_mod arg] )
  | Tmod_constraint (m, _, _, _) -> ([val_of_mod m], [packet_of_mod m])
  | Tmod_unpack (e, _) -> ([val_of_expr e], [packet_of_expr e])

(** determine whether or not to shadow the following cases by checking the existence of a guard *)
let extract c =
  let lhs = c.CL.Typedtree.c_lhs in
  let guard = c.CL.Typedtree.c_guard in
  let rhs = c.CL.Typedtree.c_rhs in
  match guard with None -> ((lhs, false), rhs) | _ -> ((lhs, true), rhs)

let se_of_expr (expr : CL.Typedtree.expression) =
  let fail s =
    CL.Location.print_loc Format.str_formatter expr.exp_loc;
    prerr_string (Format.flush_str_formatter () ^ "\n");
    failwith s
  in
  (* solves p = se and returns the set expression for p *)
  let rec solve_eq (p : CL.Typedtree.pattern) (se : value se) : pattern se list
      =
    match p.pat_desc with
    | Tpat_any -> [Top]
    | Tpat_var (x, _) ->
      update_var x [se];
      [Top]
    | Tpat_alias (p, a, _) ->
      update_var a [se];
      solve_eq p se
    | Tpat_constant c -> [Const c]
    | Tpat_tuple list -> solve_ctor None se list
    | ((Tpat_construct (_, {cstr_name}, list, _))
    [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
      solve_ctor (Some cstr_name) se list
    | ((Tpat_construct (_, {cstr_name}, list))
    [@if ocaml_version < (4, 13, 0) || defined npm]) ->
      solve_ctor (Some cstr_name) se list
    | Tpat_variant (lbl, p_o, _) -> (
      let constructor = Some lbl in
      match p_o with
      | None ->
        [Ctor_pat (constructor, [||])]
        (* give up on being consistent with the actual mem repr *)
      | Some p ->
        let temp = Var (Val (new_temp_var ())) in
        update_sc temp [Fld (se, (constructor, Some 0))];
        let sub = solve_eq p temp in
        List.map (fun x -> Ctor_pat (constructor, [|x|])) sub)
    | Tpat_record (key_val_list, _) ->
      let list =
        List.map (fun (_, lbl, pat) -> (lbl.CL.Types.lbl_pos, pat)) key_val_list
      in
      let lbl_all =
        match key_val_list with
        | (_, {CL.Types.lbl_all = l}, _) :: _ -> l
        | _ -> fail "Tried to match a record type without any fields"
      in
      let len = Array.length lbl_all in
      solve_rec len se list
    | Tpat_array list -> solve_ctor None se list
    | Tpat_lazy p ->
      let temp = Var (Val (new_temp_var ())) in
      update_sc temp [App_V (se, [])];
      solve_eq p temp
    | Tpat_or (lhs, rhs, _) -> solve_eq lhs se @ solve_eq rhs se
  and solve_ctor constructor se list =
    let l = ref list in
    let args = ref [] in
    let i = ref 0 in
    while !l != [] do
      (match !l with
      | hd :: tl ->
        let temp = Var (Val (new_temp_var ())) in
        update_sc temp [Fld (se, (constructor, Some !i))];
        let ith_se = solve_eq hd temp in
        args := ith_se :: !args;
        l := tl
      | _ -> assert false);
      i := !i + 1
    done;
    let flattened =
      List.fold_left
        (fun acc x ->
          List.fold_left
            (fun acc l -> List.map (fun y -> y :: l) x @ acc)
            [] acc)
        [[]] !args
    in
    List.map (fun l -> Ctor_pat (constructor, list_to_array l)) flattened
  and solve_rec len se list =
    (* Solve `list = se` and return the set expression of the list
       For example, `list [x, y, z] = se` should return [T, T, T] and
       `list [x, 1, true] = se` should return [T, 1, true] *)
    let l = ref list in
    let args = ref [] in
    let cursor = ref 0 in
    while !l != [] do
      match !l with
      | hd :: tl ->
        let i, p = hd in
        let temp = Var (Val (new_temp_var ())) in
        update_sc temp [Fld (se, (None, Some i))];
        let ith_se = solve_eq p temp in
        while !cursor < i do
          args := [Top] :: !args;
          incr cursor
        done;
        args := ith_se :: !args;
        incr cursor;
        l := tl
      | _ -> assert false
    done;
    while !cursor < len do
      args := [Top] :: !args;
      incr cursor
    done;
    let flattened =
      List.fold_left
        (fun acc x ->
          List.fold_left
            (fun acc l -> List.map (fun y -> y :: l) x @ acc)
            [] acc)
        [[]] !args
    in
    List.map (fun l -> Ctor_pat (None, list_to_array l)) flattened
  in
  (* solves p_i = acc, that is, p_1 = se; p_2 = se - p_1; ... *)
  let solve_param (acc : value se) (pattern, guarded) : value se =
    let p_list = solve_eq pattern acc in
    let for_each_pat acc p =
      let temp_var = Var (Val (new_temp_var ())) in
      update_sc temp_var [Diff (acc, p)];
      temp_var
    in
    if guarded then acc else List.fold_left for_each_pat acc p_list
  in
  let val_list list = List.map val_of_expr list in
  let exn_list list = List.map packet_of_expr list in
  match expr.exp_desc with
  | Texp_function {param; cases} ->
    let value_pg, body = List.split (List.map extract cases) in
    let arg = Var (Val (Expr_var param)) in
    List.fold_left solve_param arg value_pg |> ignore;
    ([Fn (Some param, List.map (fun e -> expr_of_expr e) body)], [])
  | ((Texp_match (exp, cases, exn_cases, _))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let value_pg, value_body = List.split (List.map extract cases) in
    let exn_pg, exn_body = List.split (List.map extract exn_cases) in
    let val_exp = val_of_expr exp in
    let exn_exp = packet_of_expr exp in
    let () = List.fold_left solve_param val_exp value_pg |> ignore in
    let uncaught_exn = List.fold_left solve_param exn_exp exn_pg in
    let values = val_list (value_body @ exn_body) in
    let exns = exn_list (value_body @ exn_body) in
    (values, uncaught_exn :: exns)
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
    let () = List.fold_left solve_param (val_of_expr exp) value_pg |> ignore in
    let uncaught_exn = List.fold_left solve_param (packet_of_expr exp) exn_pg in
    let values = val_list body in
    let exns = exn_list body in
    (values, uncaught_exn :: exns)
  | Texp_try (exp, cases) ->
    let exn_pg, body = List.split (List.map extract cases) in
    let uncaught_exn = List.fold_left solve_param (packet_of_expr exp) exn_pg in
    let values = val_list body in
    let exns = exn_list body in
    (val_of_expr exp :: values, uncaught_exn :: exns)
  | Texp_let (_, vbs, e) ->
    let _, p = List.split (List.map se_of_vb vbs) in
    let p = List.flatten p in
    ([val_of_expr e], packet_of_expr e :: p)
  | Texp_ident (_, _, {val_kind = Val_prim prim}) -> ([Prim prim], [])
  | Texp_ident (x, _, _) ->
    update_to_be (loc_of_expr expr) x;
    ([], [])
  | Texp_constant c -> ([Const c], [])
  | Texp_apply (e, args) ->
    let for_each_arg (_, (o : CL.Typedtree.expression option)) =
      match o with Some e -> Some (val_of_expr e) | None -> None
    in
    let acc_packet acc (_, (o : CL.Typedtree.expression option)) =
      match o with Some e -> packet_of_expr e :: acc | None -> acc
    in
    let fn = val_of_expr e in
    let exn_fn = packet_of_expr e in
    let exn_args = List.fold_left acc_packet [] args in
    let args = List.map for_each_arg args in
    ([App_V (fn, args)], App_P (fn, args) :: exn_fn :: exn_args)
  | Texp_tuple list ->
    let values = list_to_array (val_list list) in
    let mem = new_array (Array.length values) in
    let () = Array.iteri (fun i v -> update_mem mem.(i) [v]) values in
    let exns = exn_list list in
    ([Ctor (None, Static mem)], exns)
  | Texp_construct (_, {cstr_name}, list) ->
    let values = list_to_array (val_list list) in
    let mem = new_array (Array.length values) in
    let () = Array.iteri (fun i v -> update_mem mem.(i) [v]) values in
    let exns = exn_list list in
    ([Ctor (Some cstr_name, Static mem)], exns)
  | Texp_record {fields; extended_expression} ->
    let for_each_field
        ( (l : CL.Types.label_description),
          (def : CL.Typedtree.record_label_definition) ) =
      let mem = new_memory () in
      let i = l.lbl_pos in
      let kept =
        match extended_expression with
        | Some e -> Fld (val_of_expr e, (None, Some i))
        | _ -> Top
      in
      let () =
        match def with
        | Kept _ -> update_mem mem [kept]
        | Overridden (_, e) -> update_mem mem [val_of_expr e]
      in
      mem
    in
    let acc_exns acc (_, (def : CL.Typedtree.record_label_definition)) =
      match def with Overridden (_, e) -> packet_of_expr e :: acc | _ -> acc
    in
    let exns = Array.fold_left acc_exns [] fields in
    let exns =
      match extended_expression with
      | Some e -> packet_of_expr e :: exns
      | _ -> exns
    in
    ([Ctor (None, Static (Array.map for_each_field fields))], exns)
  | Texp_field (e, _, lbl) ->
    let i = lbl.lbl_pos in
    ([Fld (val_of_expr e, (None, Some i))], [packet_of_expr e])
  | Texp_variant (lbl, o) -> (
    match o with
    | Some e ->
      let mem = new_memory () in
      update_mem mem [val_of_expr e];
      ([Ctor (Some lbl, Static [|mem|])], [packet_of_expr e])
    | None -> ([Ctor (Some lbl, Static [||])], []))
  | Texp_setfield (e1, _, lbl, e2) ->
    let val1 = val_of_expr e1 in
    let val2 = val_of_expr e2 in
    let exn1 = packet_of_expr e1 in
    let exn2 = packet_of_expr e2 in
    update_sc (Fld (val1, (None, Some lbl.lbl_pos))) [val2];
    ([Ctor (Some "()", Static [||])], [exn1; exn2])
  | Texp_array list ->
    let for_each_expr_val (expr : CL.Typedtree.expression) =
      let mem = new_memory () in
      update_mem mem [val_of_expr expr];
      mem
    in
    let arr = list_to_array (List.map for_each_expr_val list) in
    ([Ctor (None, Static arr)], List.map packet_of_expr list)
  | Texp_ifthenelse (pred, if_true, Some if_false) ->
    let val1 = val_of_expr if_true in
    let val2 = val_of_expr if_false in
    let exn1 = packet_of_expr pred in
    let exn2 = packet_of_expr if_true in
    let exn3 = packet_of_expr if_false in
    ([val1; val2], [exn1; exn2; exn3])
  | Texp_ifthenelse (pred, if_true, None) ->
    ([val_of_expr if_true], [packet_of_expr pred; packet_of_expr if_true])
  | Texp_sequence (e1, e2) ->
    ([val_of_expr e2], [packet_of_expr e1; packet_of_expr e2])
  | Texp_while (pred, body) ->
    ([Ctor (Some "()", Static [||])], [packet_of_expr pred; packet_of_expr body])
  | Texp_for (i, _, start, finish, _, body) ->
    let exn_start = packet_of_expr start in
    let exn_finish = packet_of_expr finish in
    let exn_body = packet_of_expr body in
    update_var i [Top];
    ([Ctor (Some "()", Static [||])], [exn_start; exn_finish; exn_body])
  | ((Texp_letmodule (x, _, mod_loc, exp_loc))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let val_m = val_of_mod mod_loc in
    let val_e = val_of_expr exp_loc in
    let exn_m = packet_of_mod mod_loc in
    let exn_e = packet_of_expr exp_loc in
    update_var x [val_m];
    ([val_e], [exn_m; exn_e])
  | ((Texp_letmodule (x, _, _, mod_loc, exp_loc))
  [@if
    ocaml_version >= (4, 08, 0) && ocaml_version < (4, 10, 0) && not_defined npm])
    ->
    let val_m = val_of_mod mod_loc in
    let val_e = val_of_expr exp_loc in
    let exn_m = packet_of_mod mod_loc in
    let exn_e = packet_of_expr exp_loc in
    update_var x [val_m];
    ([val_e], [exn_m; exn_e])
  | ((Texp_letmodule (Some x, _, _, mod_loc, exp_loc))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let val_m = val_of_mod mod_loc in
    let val_e = val_of_expr exp_loc in
    let exn_m = packet_of_mod mod_loc in
    let exn_e = packet_of_expr exp_loc in
    update_var x [val_m];
    ([val_e], [exn_m; exn_e])
  | ((Texp_letmodule (None, _, _, mod_loc, exp_loc))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let val_e = val_of_expr exp_loc in
    let exn_m = packet_of_mod mod_loc in
    let exn_e = packet_of_expr exp_loc in
    ([val_e], [exn_m; exn_e])
  | Texp_letexception (_, exp) -> ([val_of_expr exp], [packet_of_expr exp])
  | Texp_assert exp ->
    (* How to express Assert_failure... *)
    ([], [Ctor (Some "Assert_failure", Static [||]); packet_of_expr exp])
  | Texp_lazy exp -> ([Fn (None, [expr_of_expr exp])], [])
  | Texp_pack m -> ([val_of_mod m], [packet_of_mod m])
  | ((Texp_letop {let_; ands; body})
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let let_path = let_.bop_op_path in
    let letop = Var (Val (Expr (Bop_loc let_.bop_op_val))) in
    let bound = (val_of_expr let_.bop_exp, [packet_of_expr let_.bop_exp]) in
    let for_each_and (acc_val, acc_exn_list) (andop : CL.Typedtree.binding_op) =
      let and_path = andop.bop_op_path in
      let and_val = Var (Val (Expr (Bop_loc andop.bop_op_val))) in
      let bound_val = val_of_expr andop.bop_exp in
      let exn = packet_of_expr andop.bop_exp in
      let updated_val = App_V (and_val, [Some acc_val; Some bound_val]) in
      update_to_be (Bop_loc andop.bop_op_val) and_path;
      (updated_val, exn :: acc_exn_list)
    in
    let bound_expr, exns = List.fold_left for_each_and bound ands in
    let (Expr_var temp) = new_temp_var () in
    let body_fn = Fn (Some temp, [expr_of_expr body.c_rhs]) in
    let value = App_V (letop, [Some bound_expr; Some body_fn]) in
    let exn = App_P (letop, [Some bound_expr; Some body_fn]) in
    solve_eq body.c_lhs (Var (Val (Expr_var temp))) |> ignore;
    update_to_be (Bop_loc let_.bop_op_val) let_path;
    ([value], exn :: exns)
  | ((Texp_open (_, exp)) [@if ocaml_version >= (4, 08, 0) && not_defined npm])
    ->
    ([val_of_expr exp], [packet_of_expr exp])
  | _ -> ([], [])

(* expr, module_binding, module_expr, structure, structure_item, value_binding, value_bindings *)
(* se_of_something returns the set expressions corresponding to the location of "something" *)
(* tast_mapper connects val/exns returned by se_of_something with the code_loc of the AST node *)
(* var_to_se) correlates ident to se set_constraints) correlates location to se *)
(* after all cmt files are processed, lookup to_be_resolved to resolve Path.t. *)
