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
          let ith = Loc (List.nth l i) in
          SESet.singleton ith
        else SESet.empty
      with _ -> SESet.empty)
    | _ -> SESet.empty)
  | Arr l -> SESet.singleton (Loc l)
  | _ -> SESet.empty

let propagate = function
  | Top | Const _ | Ctor _ | Arr _ | Prim _ | Fn _
  | App_v (_, None :: _)
  | Prim_v _ ->
    true
  | _ -> false

(** given a collection of set expressions under env, elaborate upon possible expressions *)
let elaborate se =
  match se with
  | Top | Const _ | Ctor _ | Arr _ | Prim _ | Fn _
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
        | Ctor (None, l) -> (
          try update_sc (Loc (List.nth l i)) set with _ -> ())
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
