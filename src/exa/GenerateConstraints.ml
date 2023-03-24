(*
 * Copyright (c) Programming Research Laboratory (ROPAS)
 *               Seoul National University, Korea
 * Copyright (c) ReScript Association
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

[%%import "../../config.h"]

open Hashtbl
open SetExpression

(** se_of_something returns (value_of_something, packet_of_something) *)

(** The "value" of a binding is the union of all the "constructs" that are tagged with the bound names *)
let se_of_mb (mb : CL.Typedtree.module_binding) =
  match mb with
  | ({mb_id = Some id; mb_expr}
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let mem = new_memory !current_module in
    let value = val_of_mod mb_expr in
    init_id id value;
    init_sc (Loc mem) [Var value];
    ( [Ctor (Some (CL.Ident.name id), [(mem, None)])],
      [Var (packet_of_mod mb_expr)] )
  | ({mb_id; mb_expr} [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    let mem = new_memory !current_module in
    let value = val_of_mod mb_expr in
    init_id mb_id value;
    init_sc (Loc mem) [Var value];
    ( [Ctor (Some (CL.Ident.name mb_id), [(mem, None)])],
      [Var (packet_of_mod mb_expr)] )
  | {mb_expr} -> ([], [Var (packet_of_mod mb_expr)])

let se_of_vb (vb : CL.Typedtree.value_binding) =
  let local_binding : (string, value se list) t = create 10 in
  (* update the table *)
  let update_tbl key data =
    if mem local_binding key then (
      let original = find local_binding key in
      remove local_binding key;
      add local_binding key (data :: original))
    else add local_binding key [data]
  in
  (* update the table while traversing the pattern *)
  let rec solve_eq (pat : CL.Typedtree.pattern) e =
    (* Does not return its set expression, as it does not require screening *)
    match pat.pat_desc with
    | Tpat_any | Tpat_constant _ -> ()
    | Tpat_var (x, _) ->
      init_id x e;
      update_tbl (CL.Ident.name x) (Var e)
    | Tpat_alias (p, a, _) ->
      init_id a e;
      update_tbl (CL.Ident.name a) (Var e);
      solve_eq p e
    | Tpat_tuple list -> solve_ctor None e list
    | ((Tpat_construct (_, {cstr_name}, list, _))
    [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
      solve_ctor (Some cstr_name) e list
    | ((Tpat_construct (_, {cstr_name}, list))
    [@if ocaml_version < (4, 13, 0) || defined npm]) ->
      solve_ctor (Some cstr_name) e list
    | Tpat_variant (lbl, p_o, _) -> (
      let constructor = Some lbl in
      match p_o with
      | None -> ()
      | Some p ->
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (e, (constructor, Some 0))];
        solve_eq p temp)
    | Tpat_record (key_val_list, _) ->
      let list =
        List.map (fun (_, lbl, pat) -> (lbl.CL.Types.lbl_pos, pat)) key_val_list
      in
      solve_rec e list
    | Tpat_array list -> solve_ctor None e list
    | Tpat_lazy p ->
      let temp = new_temp_var () in
      init_sc (Var temp) [App_v (e, [])];
      solve_eq p temp
    | Tpat_or (lhs, rhs, _) ->
      solve_eq lhs e;
      solve_eq rhs e
  and solve_ctor constructor e list =
    let l = ref list in
    let i = ref 0 in
    while !l <> [] do
      (match !l with
      | hd :: tl ->
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (e, (constructor, Some !i))];
        solve_eq hd temp;
        l := tl
      | _ -> assert false);
      i := !i + 1
    done
  and solve_rec e list =
    let l = ref list in
    while !l <> [] do
      match !l with
      | hd :: tl ->
        let i, p = hd in
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (e, (None, Some i))];
        solve_eq p temp;
        l := tl
      | _ -> assert false
    done
  in
  solve_eq vb.vb_pat (val_of_expr vb.vb_expr);
  let for_each_binding acc (name, list) =
    (let mem = new_memory !current_module in
     init_sc (Loc mem) list;
     Ctor (Some name, [(mem, None)]))
    :: acc
  in
  let seq_of_bindings = to_seq local_binding in
  let ctor_list = Seq.fold_left for_each_binding [] seq_of_bindings in
  (ctor_list, [Var (packet_of_expr vb.vb_expr)])

let se_of_struct_item (item : CL.Typedtree.structure_item) =
  match item.str_desc with
  | Tstr_eval (e, _) -> ([], [Var (packet_of_expr e)])
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
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (value, (Some (CL.Ident.name x), Some 0))];
        init_id x temp
      | (Sig_value (x, _, _) | Sig_module (x, _, _, _, _))
      [@if ocaml_version >= (4, 08, 0) && not_defined npm] ->
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (value, (Some (CL.Ident.name x), Some 0))];
        init_id x temp
      | _ -> ()
    in
    List.iter for_each_sig_item incl_type;
    ([Var value], [])
  | _ -> ([], [])

(* a struct is a union of constructs *)
let se_of_struct (str : CL.Typedtree.structure) =
  let v, p = List.split (List.map se_of_struct_item str.str_items) in
  (List.flatten v, List.flatten p)

let se_of_module_expr (m : CL.Typedtree.module_expr) =
  match m.mod_desc with
  | ((Tmod_functor (Named (Some x, _, _), me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let temp = new_temp_var () in
    init_id x temp;
    ([Fn (Some (x, !current_module), [loc_of_mod me])], [])
  | (Tmod_functor (Named (None, _, _), me) | Tmod_functor (Unit, me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm] ->
    ([Fn (None, [loc_of_mod me])], [])
  | ((Tmod_functor (x, _, _, me))
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    let temp = new_temp_var () in
    init_id x temp;
    ([Fn (Some (x, !current_module), [loc_of_mod me])], [])
  | Tmod_ident (x, _) ->
    let x = val_of_path x in
    ([Var x], [])
  | Tmod_structure structure -> se_of_struct structure
  | Tmod_apply (func, arg, _) ->
    ( [App_v (val_of_mod func, [Some (val_of_mod arg)])],
      [Var (packet_of_mod func); Var (packet_of_mod arg)] )
  | Tmod_constraint (m, _, _, _) ->
    ([Var (val_of_mod m)], [Var (packet_of_mod m)])
  | Tmod_unpack (e, _) -> ([Var (val_of_expr e)], [Var (packet_of_expr e)])

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
  let rec solve_eq (p : CL.Typedtree.pattern) (e : tagged_expr) :
      pattern se list =
    match p.pat_desc with
    | Tpat_any -> [Top]
    | Tpat_var (x, _) ->
      init_id x e;
      [Top]
    | Tpat_alias (p, a, _) ->
      init_id a e;
      solve_eq p e
    | Tpat_constant c -> [Const c]
    | Tpat_tuple list -> solve_ctor None e list
    | ((Tpat_construct (_, {cstr_name}, list, _))
    [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
      solve_ctor (Some cstr_name) e list
    | ((Tpat_construct (_, {cstr_name}, list))
    [@if ocaml_version < (4, 13, 0) || defined npm]) ->
      solve_ctor (Some cstr_name) e list
    | Tpat_variant (lbl, p_o, _) -> (
      let constructor = Some lbl in
      match p_o with
      | None ->
        [Ctor_pat (constructor, [])]
        (* give up on being consistent with the actual mem repr *)
      | Some p ->
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (e, (constructor, Some 0))];
        let sub = solve_eq p temp in
        List.map (fun x -> Ctor_pat (constructor, [x])) sub)
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
      solve_rec len e list
    | Tpat_array list -> solve_ctor None e list
    | Tpat_lazy p ->
      let temp = new_temp_var () in
      init_sc (Var temp) [App_v (e, [])];
      solve_eq p temp
    | Tpat_or (lhs, rhs, _) -> solve_eq lhs e @ solve_eq rhs e
  and solve_ctor constructor e list =
    let l = ref list in
    let args = ref [] in
    let i = ref 0 in
    while !l <> [] do
      (match !l with
      | hd :: tl ->
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (e, (constructor, Some !i))];
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
    List.map (fun l -> Ctor_pat (constructor, l)) flattened
  and solve_rec len e list =
    (* Solve `list = se` and return the set expression of the list
       For example, `list [x, y, z] = se` should return [T, T, T] and
       `list [x, 1, true] = se` should return [T, 1, true] *)
    let l = ref list in
    let args = ref [] in
    let cursor = ref 0 in
    while !l <> [] do
      match !l with
      | hd :: tl ->
        let i, p = hd in
        let temp = new_temp_var () in
        init_sc (Var temp) [Fld (e, (None, Some i))];
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
    List.map (fun l -> Ctor_pat (None, l)) flattened
  in
  (* solves p_i = acc, that is, p_1 = se; p_2 = se - p_1; ... *)
  let solve_param (acc : tagged_expr) (pattern, guarded) : tagged_expr =
    let p_list = solve_eq pattern acc in
    let for_each_pat acc p =
      let temp_var = new_temp_var () in
      init_sc (Var temp_var) [Diff (acc, p)];
      temp_var
    in
    if guarded then acc else List.fold_left for_each_pat acc p_list
  in
  let val_list list = List.map (fun e -> Var (val_of_expr e)) list in
  let exn_list list = List.map (fun e -> Var (packet_of_expr e)) list in
  match expr.exp_desc with
  | Texp_function {param; cases} ->
    let value_pg, body = List.split (List.map extract cases) in
    let arg = new_temp_var () in
    init_id param arg;
    List.fold_left solve_param arg value_pg |> ignore;
    ( [
        Fn
          (Some (param, !current_module), List.map (fun e -> loc_of_expr e) body);
      ],
      [] )
  | ((Texp_match (exp, cases, exn_cases, _))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let value_pg, value_body = List.split (List.map extract cases) in
    let exn_pg, exn_body = List.split (List.map extract exn_cases) in
    let val_exp = val_of_expr exp in
    let exn_exp = packet_of_expr exp in
    let () = List.fold_left solve_param val_exp value_pg |> ignore in
    let uncaught_exn = Var (List.fold_left solve_param exn_exp exn_pg) in
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
    let uncaught_exn =
      Var (List.fold_left solve_param (packet_of_expr exp) exn_pg)
    in
    let values = val_list body in
    let exns = exn_list body in
    (values, uncaught_exn :: exns)
  | Texp_try (exp, cases) ->
    let exn_pg, body = List.split (List.map extract cases) in
    let uncaught_exn =
      Var (List.fold_left solve_param (packet_of_expr exp) exn_pg)
    in
    let values = val_list body in
    let exns = exn_list body in
    (Var (val_of_expr exp) :: values, uncaught_exn :: exns)
  | Texp_let (_, vbs, e) ->
    let _, p = List.split (List.map se_of_vb vbs) in
    let p = List.flatten p in
    ([Var (val_of_expr e)], Var (packet_of_expr e) :: p)
  | Texp_ident (_, _, {val_kind = Val_prim prim}) -> ([Prim prim], [])
  | Texp_ident (x, _, _) -> ([Var (val_of_path x)], [])
  | Texp_constant c -> ([Const c], [])
  | Texp_apply (e, args) ->
    let for_each_arg (_, (o : CL.Typedtree.expression option)) =
      match o with Some e -> Some (val_of_expr e) | None -> None
    in
    let acc_packet acc (_, (o : CL.Typedtree.expression option)) =
      match o with Some e -> Var (packet_of_expr e) :: acc | None -> acc
    in
    let fn = val_of_expr e in
    let exn_fn = Var (packet_of_expr e) in
    let exn_args = List.fold_left acc_packet [] args in
    let args = List.map for_each_arg args in
    ([App_v (fn, args)], App_p (fn, args) :: exn_fn :: exn_args)
  | Texp_tuple list ->
    let values = list_to_array (val_list list) in
    let mem = new_array (Array.length values) in
    let () = Array.iteri (fun i v -> init_sc (Loc mem.(i)) [v]) values in
    let exns = exn_list list in
    ([Ctor (None, List.map (fun l -> (l, None)) (Array.to_list mem))], exns)
  | Texp_construct (_, {cstr_name}, list) ->
    let values = list_to_array (val_list list) in
    let mem = new_array (Array.length values) in
    let () = Array.iteri (fun i v -> init_sc (Loc mem.(i)) [v]) values in
    let exns = exn_list list in
    ( [Ctor (Some cstr_name, List.map (fun l -> (l, None)) (Array.to_list mem))],
      exns )
  | Texp_record {fields; extended_expression} ->
    let for_each_field
        ( (l : CL.Types.label_description),
          (def : CL.Typedtree.record_label_definition) ) =
      let mem = new_memory !current_module in
      let i = l.lbl_pos in
      let kept =
        match extended_expression with
        | Some e -> [Fld (val_of_expr e, (None, Some i))]
        | None -> []
      in
      let () =
        match def with
        | ((Kept _) [@if ocaml_version < (5, 0, 0) || defined npm]) ->
          init_sc (Loc mem) kept
        | ((Kept (_, _)) [@if ocaml_version >= (5, 0, 0) && not_defined npm]) ->
          init_sc (Loc mem) kept
        | Overridden (_, e) -> init_sc (Loc mem) [Var (val_of_expr e)]
      in
      mem
    in
    let acc_exns acc (_, (def : CL.Typedtree.record_label_definition)) =
      match def with
      | Overridden (_, e) -> Var (packet_of_expr e) :: acc
      | _ -> acc
    in
    let exns = Array.fold_left acc_exns [] fields in
    let exns =
      match extended_expression with
      | Some e -> Var (packet_of_expr e) :: exns
      | _ -> exns
    in
    ( [
        Ctor
          ( None,
            List.map
              (fun l -> (l, None))
              (Array.to_list (Array.map for_each_field fields)) );
      ],
      exns )
  | Texp_field (e, _, lbl) ->
    let i = lbl.lbl_pos in
    ([Fld (val_of_expr e, (None, Some i))], [Var (packet_of_expr e)])
  | Texp_variant (lbl, o) -> (
    match o with
    | Some e ->
      let mem = new_memory !current_module in
      init_sc (Loc mem) [Var (val_of_expr e)];
      ([Ctor (Some lbl, [(mem, None)])], [Var (packet_of_expr e)])
    | None -> ([Ctor (Some lbl, [])], []))
  | Texp_setfield (e1, _, lbl, e2) ->
    let val1 = val_of_expr e1 in
    let val2 = Var (val_of_expr e2) in
    let exn1 = Var (packet_of_expr e1) in
    let exn2 = Var (packet_of_expr e2) in
    init_sc (Fld (val1, (None, Some lbl.lbl_pos))) [val2];
    ([Ctor (Some "()", [])], [exn1; exn2])
  | Texp_array list ->
    let for_each_expr_val (expr : CL.Typedtree.expression) =
      let mem = new_memory !current_module in
      init_sc (Loc mem) [Var (val_of_expr expr)];
      mem
    in
    let arr = list_to_array (List.map for_each_expr_val list) in
    ( [Ctor (None, List.map (fun l -> (l, None)) (Array.to_list arr))],
      exn_list list )
  | Texp_ifthenelse (pred, if_true, Some if_false) ->
    let val1 = Var (val_of_expr if_true) in
    let val2 = Var (val_of_expr if_false) in
    let exn1 = Var (packet_of_expr pred) in
    let exn2 = Var (packet_of_expr if_true) in
    let exn3 = Var (packet_of_expr if_false) in
    ([val1; val2], [exn1; exn2; exn3])
  | Texp_ifthenelse (pred, if_true, None) ->
    ( [Var (val_of_expr if_true)],
      [Var (packet_of_expr pred); Var (packet_of_expr if_true)] )
  | Texp_sequence (e1, e2) ->
    ([Var (val_of_expr e2)], [Var (packet_of_expr e1); Var (packet_of_expr e2)])
  | Texp_while (pred, body) ->
    ( [Ctor (Some "()", [])],
      [Var (packet_of_expr pred); Var (packet_of_expr body)] )
  | Texp_for (i, _, start, finish, _, body) ->
    let exn_start = Var (packet_of_expr start) in
    let exn_finish = Var (packet_of_expr finish) in
    let exn_body = Var (packet_of_expr body) in
    let temp = new_temp_var () in
    init_id i temp;
    init_sc (Var temp) [Top];
    ([Ctor (Some "()", [])], [exn_start; exn_finish; exn_body])
  | ((Texp_letmodule (x, _, mod_loc, exp_loc))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let val_m = val_of_mod mod_loc in
    let val_e = Var (val_of_expr exp_loc) in
    let exn_m = Var (packet_of_mod mod_loc) in
    let exn_e = Var (packet_of_expr exp_loc) in
    init_id x val_m;
    ([val_e], [exn_m; exn_e])
  | ((Texp_letmodule (x, _, _, mod_loc, exp_loc))
  [@if
    ocaml_version >= (4, 08, 0) && ocaml_version < (4, 10, 0) && not_defined npm])
    ->
    let val_m = val_of_mod mod_loc in
    let val_e = Var (val_of_expr exp_loc) in
    let exn_m = Var (packet_of_mod mod_loc) in
    let exn_e = Var (packet_of_expr exp_loc) in
    init_id x val_m;
    ([val_e], [exn_m; exn_e])
  | ((Texp_letmodule (Some x, _, _, mod_loc, exp_loc))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let val_m = val_of_mod mod_loc in
    let val_e = Var (val_of_expr exp_loc) in
    let exn_m = Var (packet_of_mod mod_loc) in
    let exn_e = Var (packet_of_expr exp_loc) in
    init_id x val_m;
    ([val_e], [exn_m; exn_e])
  | ((Texp_letmodule (None, _, _, mod_loc, exp_loc))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let val_e = Var (val_of_expr exp_loc) in
    let exn_m = Var (packet_of_mod mod_loc) in
    let exn_e = Var (packet_of_expr exp_loc) in
    ([val_e], [exn_m; exn_e])
  | Texp_letexception (_, exp) ->
    ([Var (val_of_expr exp)], [Var (packet_of_expr exp)])
  | Texp_assert exp ->
    (* How to express Assert_failure... *)
    ([], [Ctor (Some "Assert_failure", []); Var (packet_of_expr exp)])
  | Texp_lazy exp -> ([Fn (None, [loc_of_expr exp])], [])
  | Texp_pack m -> ([Var (val_of_mod m)], [Var (packet_of_mod m)])
  | ((Texp_letop {let_; ands; param; body})
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let let_path = let_.bop_op_path in
    let let_loc = loc_of_summary (Bop_loc let_.bop_op_val) in
    let letop = Val let_loc in
    let bound =
      (val_of_expr let_.bop_exp, [Var (packet_of_expr let_.bop_exp)])
    in
    let for_each_and (acc_val, acc_exn_list) (and_ : CL.Typedtree.binding_op) =
      let and_path = and_.bop_op_path in
      let and_loc = loc_of_summary (Bop_loc and_.bop_op_val) in
      let andop = Val and_loc in
      let bound_val = val_of_expr and_.bop_exp in
      let exn = packet_of_expr and_.bop_exp in
      let exn_app = App_p (andop, [Some acc_val; Some bound_val]) in
      let temp = new_temp_var () in
      let updated_val = App_v (andop, [Some acc_val; Some bound_val]) in
      init_sc (Var temp) [updated_val];
      init_sc (Var andop) [Var (val_of_path and_path)];
      (temp, exn_app :: Var exn :: acc_exn_list)
    in
    let bound_expr, exns = List.fold_left for_each_and bound ands in
    let body_fn =
      Fn (Some (param, !current_module), [loc_of_expr body.c_rhs])
    in
    let temp_fn = new_temp_var () in
    let value =
      init_sc (Var temp_fn) [body_fn];
      App_v (letop, [Some bound_expr; Some temp_fn])
    in
    let exn = App_p (letop, [Some bound_expr; Some temp_fn]) in
    let temp_param = new_temp_var () in
    init_id param temp_param;
    solve_eq body.c_lhs temp_param |> ignore;
    init_sc (Var letop) [Var (val_of_path let_path)];
    ([value], exn :: exns)
  | ((Texp_open (_, exp)) [@if ocaml_version >= (4, 08, 0) && not_defined npm])
    ->
    ([Var (val_of_expr exp)], [Var (packet_of_expr exp)])
  | _ -> ([], [])

(* expr, module_binding, module_expr, structure, structure_item, value_binding, value_bindings *)
(* se_of_something returns the set expressions corresponding to the location of "something" *)
(* tast_mapper connects val/exns returned by se_of_something with the code_loc of the AST node *)
(* var_to_se) correlates ident to se set_constraints) correlates location to se *)
(* after all cmt files are processed, lookup to_be_resolved to resolve Path.t. *)
