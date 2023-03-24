(*
 * Copyright (c) Programming Research Laboratory (ROPAS)
 *               Seoul National University, Korea
 * Copyright (c) ReScript Association
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open SetExpression

let rec arg_len = function
  | [] -> 0
  | None :: tl -> arg_len tl
  | Some _ :: tl -> arg_len tl + 1

let rec merge_args = function
  | [], l -> l
  | l, [] -> l
  | None :: tl, hd :: l -> hd :: merge_args (tl, l)
  | Some x :: tl, l -> Some x :: merge_args (tl, l)

(* arrays or external functions returning records cannot be filtered *)
let time_spent_in_var = ref 0.0
let time_spent_in_filter = ref 0.0
let time_spent_in_fld = ref 0.0
let time_spent_in_closure = ref 0.0
let time_spent_in_update = ref 0.0
let time_spent_in_const = ref 0.0
let temp_timer = ref 0.0
let start_timer () = temp_timer := Unix.gettimeofday ()

let stop_timer measure =
  measure := !measure +. (Unix.gettimeofday () -. !temp_timer)

let elaborate_app f hd tl =
  match f with
  | Fn (Some x, body) ->
    let value =
      SESet.of_list
        (List.map
           (fun loc -> if tl = [] then Var (Val loc) else App_v (Val loc, tl))
           body)
    in
    let bound = lookup_id x in
    update_sc (Var bound) (SESet.singleton (Var hd));
    value
  | Prim p ->
    let args = Some hd :: tl in
    if arg_len args = p.prim_arity then PrimResolution.value_prim (p, args)
    else SESet.singleton (Prim_v (p, args))
  | App_v (e, None :: tl') ->
    SESet.singleton (App_v (e, Some hd :: merge_args (tl', tl)))
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    if arg_len args = p.prim_arity then PrimResolution.value_prim (p, args)
    else SESet.singleton (Prim_v (p, args))
  | _ -> SESet.empty

let elaborate_app_p f hd tl =
  match f with
  | Fn (Some x, body) ->
    let app =
      if tl = [] then SESet.empty
      else SESet.of_list (List.map (fun e -> App_p (Val e, tl)) body)
    in
    let body = SESet.of_list (List.map (fun e -> Var (Packet e)) body) in
    let packet = SESet.union body app in
    let bound = lookup_id x in
    update_sc (Var bound) (SESet.singleton (Var hd));
    packet
  | Prim p ->
    let args = Some hd :: tl in
    if arg_len args = p.prim_arity then PrimResolution.packet_prim (p, args)
    else SESet.empty
  | App_v (e, None :: tl') ->
    SESet.singleton (App_p (e, Some hd :: merge_args (tl', tl)))
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    if arg_len args = p.prim_arity then PrimResolution.packet_prim (p, args)
    else SESet.empty
  | _ -> SESet.empty

let elaborate_lazy f =
  match f with
  | Fn (None, body) -> SESet.of_list (List.map (fun loc -> Var (Val loc)) body)
  | _ -> SESet.empty

let elaborate_lazy_p f =
  match f with
  | Fn (None, body) ->
    SESet.of_list (List.map (fun loc -> Var (Packet loc)) body)
  | _ -> SESet.empty

let elaborate_fld se fld =
  match se with
  | Top -> SESet.singleton Top
  | Ctor (kappa, l) -> (
    match fld with
    | kappa', Some i -> (
      try
        if kappa = kappa' then
          let ith =
            match List.nth l i with
            | l, None -> Loc l
            | _, Some p -> pat_to_val p
          in
          SESet.singleton ith
        else SESet.empty
      with _ -> SESet.empty)
    | _ -> SESet.empty)
  | Ctor_pat (kappa, l) -> (
    match fld with
    | kappa', Some i -> (
      try
        if kappa = kappa' then
          let ith = pat_to_val (List.nth l i) in
          SESet.singleton ith
        else SESet.empty
      with _ -> SESet.empty)
    | _ -> SESet.empty)
  | Arr l -> SESet.singleton (Loc l)
  | _ -> SESet.empty

let propagate = function
  | Top | Const _ | Ctor_pat _ | Ctor _ | Arr _ | Prim _ | Fn _
  | App_v (_, None :: _)
  | Prim_v _ ->
    true
  | _ -> false

let rec filter_pat = function
  | _, Top -> SESet.empty
  | Const c, Const c' ->
    if c = c' then SESet.empty else SESet.singleton (Const c)
  | Ctor_pat (kappa, l), Ctor_pat (kappa', l') ->
    if kappa <> kappa' || List.length l <> List.length l' then
      SESet.singleton (Ctor_pat (kappa, l))
    else
      let filtered_lists =
        List.map (fun l -> Ctor_pat (kappa, l)) (diff_pat_list ([], l) l')
      in
      SESet.of_list filtered_lists
  | Ctor (kappa, l), Ctor_pat (kappa', l') ->
    if kappa <> kappa' || List.length l <> List.length l' then
      SESet.singleton (Ctor (kappa, l))
    else
      let filtered_lists =
        List.map (fun l -> Ctor (kappa, l)) (diff_list ([], l) l')
      in
      SESet.of_list filtered_lists
  | x, _ -> SESet.singleton x

and diff_pat_list (rev_hd, tl) tl' =
  match (tl, tl') with
  | [], [] -> []
  | hd :: tl1, hd' :: tl2 ->
    let diff = filter_pat (pat_to_val hd, hd') in
    let inter = hd' in
    let diff_rest = diff_pat_list (inter :: rev_hd, tl1) tl2 in
    SESet.fold
      (fun x acc ->
        match val_to_pat x with
        | Some p -> List.rev_append rev_hd (p :: tl1) :: acc
        | None -> acc)
      diff diff_rest
  | _ -> assert false

and diff_list (rev_hd, tl) tl' =
  match (tl, tl') with
  | [], [] -> []
  | (l, None) :: tl1, p :: tl2 ->
    let abstraction = function
      | Ctor (kappa, l) ->
        Ctor_pat (kappa, List.map (function _, None -> Top | _, Some p -> p) l)
      | x -> ( match val_to_pat x with None -> Top | Some p -> p)
    in
    let diff =
      SESet.fold
        (fun se acc -> SESet.union (filter_pat (se, p)) acc)
        (SESet.filter propagate (lookup_sc (Loc l)))
        SESet.empty
    in
    let inter = (l, Some p) in
    let diff_rest = diff_list (inter :: rev_hd, tl1) tl2 in
    SESet.fold
      (fun x acc ->
        List.rev_append rev_hd ((l, Some (abstraction x)) :: tl1) :: acc)
      diff diff_rest
  | (l, Some p1) :: tl1, p2 :: tl2 ->
    let diff = filter_pat (pat_to_val p1, p2) in
    let inter = (l, Some p2) in
    let diff_rest = diff_list (inter :: rev_hd, tl1) tl2 in
    SESet.fold
      (fun x acc ->
        List.rev_append rev_hd
          ((l, val_to_pat x (* must always be Some p *)) :: tl1)
        :: acc)
      diff diff_rest
  | _ -> assert false

(** given a collection of set expressions under env, elaborate upon possible expressions *)
let elaborate se =
  match se with
  | Top | Const _ | Ctor_pat _ | Ctor _ | Arr _ | Prim _ | Fn _
  | App_v (_, None :: _)
  | App_p (_, None :: _)
  | Prim_v _ | Prim_p _ ->
    SESet.empty
  | Id x -> (
    try
      let bound = lookup_id x in
      SESet.singleton (Var bound)
    with Not_found -> SESet.empty)
  | App_v (e, Some e' :: tl) when Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        start_timer ();
        let to_add = elaborate_app se e' tl in
        stop_timer time_spent_in_closure;
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | App_p (e, Some e' :: tl) when Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        start_timer ();
        let to_add = elaborate_app_p se e' tl in
        stop_timer time_spent_in_closure;
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | App_v (e, []) when Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        start_timer ();
        let to_add = elaborate_lazy se in
        stop_timer time_spent_in_closure;
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | App_p (e, []) when Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        start_timer ();
        let to_add = elaborate_lazy_p se in
        stop_timer time_spent_in_closure;
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | Fld (e, fld) when Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        start_timer ();
        let to_add = elaborate_fld se fld in
        stop_timer time_spent_in_fld;
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | Diff (e, p) when Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        start_timer ();
        let filtered = filter_pat (se, p) in
        stop_timer time_spent_in_filter;
        SESet.union filtered acc)
      (SESet.filter propagate (lookup_sc (Var e)))
      SESet.empty
  | Var e when Worklist.mem (Var e) prev_worklist ->
    start_timer ();
    let set = SESet.filter propagate (lookup_sc (Var e)) in
    stop_timer time_spent_in_var;
    set
  | Loc l when Worklist.mem (Loc l) prev_worklist ->
    start_timer ();
    let set = SESet.filter propagate (lookup_sc (Loc l)) in
    stop_timer time_spent_in_var;
    set
  | _ -> SESet.empty

let back_propagated_vars = Hashtbl.create 10

let rec auxiliary_back_propagate var =
  match Hashtbl.find back_propagated_vars var with
  | exception Not_found ->
    Hashtbl.add back_propagated_vars var ();
    SESet.iter
      (function Var x -> auxiliary_back_propagate (Var x) | _ -> ())
      (try lookup_sc var with _ -> SESet.empty)
  | () -> ()

let back_propagate var set =
  Hashtbl.clear back_propagated_vars;
  auxiliary_back_propagate (Var var);
  Hashtbl.iter
    (function Var x -> fun () -> update_sc (Var x) set | _ -> fun () -> ())
    back_propagated_vars

let step_sc_for_entry x set =
  match x with
  | Var _ | Loc _ ->
    let elaborated =
      SESet.fold
        (fun se acc ->
          let elaborated = elaborate se in
          SESet.union elaborated acc)
        set SESet.empty
    in
    update_sc x elaborated
  | Fld (e, (None, Some i)) ->
    start_timer ();
    SESet.iter
      (function
        | Ctor (k, l) -> (
          try
            match List.nth l i with
            | loc, Some _ ->
              let j = ref (-1) in
              let temp_l =
                List.fold_left
                  (fun acc x ->
                    incr j;
                    if !j = i then (loc, None) :: acc else x :: acc)
                  [] l
              in
              let temp = Ctor (k, List.rev temp_l) in
              back_propagate e (SESet.singleton temp)
            | loc, None -> update_sc (Loc loc) set
          with _ -> ())
        | _ -> ())
      (lookup_sc (Var e));
    stop_timer time_spent_in_update
  | _ -> failwith "Invalid LHS"

let step_sc () =
  let to_be_reduced =
    SESet.fold
      (fun idx acc ->
        SESet.union
          (try Hashtbl.find reverse_sc idx with Not_found -> SESet.empty)
          acc)
      !prev_worklist SESet.empty
  in
  SESet.iter (fun x -> step_sc_for_entry x (lookup_sc x)) to_be_reduced

let prepare_step () =
  changed := false;
  Worklist.prepare_step worklist prev_worklist

let solve () =
  Format.flush_str_formatter () |> ignore;
  prepare_step ();
  step_sc ();
  while !changed do
    prepare_step ();
    step_sc ()
  done
