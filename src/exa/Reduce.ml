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
let allocated = Hashtbl.create 10

let value_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_v (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_v (x, [Some y]))
  | {CL.Primitive.prim_name = "%identity" | "%opaque"}, [Some x] ->
    SESet.singleton (Var x)
  | {CL.Primitive.prim_name = "%ignore"}, [Some _] ->
    SESet.singleton (Ctor (Some "()", []))
  | {CL.Primitive.prim_name = "%field0"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 0)))
  | {CL.Primitive.prim_name = "%field1"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 1)))
  | {CL.Primitive.prim_name = "%setfield0"}, [Some x; Some y] ->
    update_sc (Fld (x, (None, Some 0))) (SESet.singleton (Var y));
    SESet.singleton (Ctor (Some "()", []))
  | {CL.Primitive.prim_name = "%makemutable"}, [Some x] -> (
    let value = SESet.singleton (Var x) in
    match Hashtbl.find allocated x with
    | exception Not_found ->
      let i = new_memory (get_context (Var x)) in
      Hashtbl.add allocated x i;
      update_sc (Loc i) value;
      SESet.singleton (Ctor (None, [(i, None)]))
    | i ->
      update_sc (Loc i) value;
      SESet.singleton (Ctor (None, [(i, None)])))
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_v (x, []))
  | ( {
        CL.Primitive.prim_name =
          ( "%eq" | "%noteq" | "%ltint" | "%leint" | "%gtint" | "%geint"
          | "%eqfloat" | "%noteqfloat" | "%ltfloat" | "%lefloat" | "%gtfloat"
          | "%gefloat" | "%equal" | "%notequal" | "%lessequal" | "%lessthan"
          | "%greaterequal" | "%greaterthan" | "%compare" | "%boolnot"
          | "%sequand" | "%sequor" );
      },
      _ ) ->
    SESet.of_list [Ctor (Some "true", []); Ctor (Some "false", [])]
  | ( {
        CL.Primitive.prim_name =
          "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace";
      },
      _ ) ->
    SESet.empty
  | _ -> SESet.singleton Top

let packet_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_p (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_p (x, [Some y]))
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_p (x, []))
  | ( {
        CL.Primitive.prim_name =
          "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace";
      },
      Some x :: _ ) ->
    SESet.singleton (Var x)
  | {CL.Primitive.prim_name = "caml_sys_exit"}, _ ->
    SESet.singleton (Ctor (Some "Exit", []))
  | _ -> SESet.empty

let time_spent_in_var = ref 0.0
let time_spent_in_filter = ref 0.0
let time_spent_in_fld = ref 0.0
let time_spent_in_closure = ref 0.0
let time_spent_in_update = ref 0.0
let time_spent_in_const = ref 0.0

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
    if arg_len args = p.prim_arity then value_prim (p, args)
    else SESet.singleton (Prim_v (p, args))
  | App_v (e, None :: tl') ->
    SESet.singleton (App_v (e, Some hd :: merge_args (tl', tl)))
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    if arg_len args = p.prim_arity then value_prim (p, args)
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
    if arg_len args = p.prim_arity then packet_prim (p, args) else SESet.empty
  | App_v (e, None :: tl') ->
    SESet.singleton (App_p (e, Some hd :: merge_args (tl', tl)))
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    if arg_len args = p.prim_arity then packet_prim (p, args) else SESet.empty
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
          let ith = Loc (fst (List.nth l i)) in
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
    let inter = hd' (* unsafe *) in
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

let use_worklist = true

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
  | App_v (e, Some e' :: tl)
    when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        let to_add = elaborate_app se e' tl in
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | App_p (e, Some e' :: tl)
    when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        let to_add = elaborate_app_p se e' tl in
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | App_v (e, []) when (not use_worklist) || Worklist.mem (Var e) prev_worklist
    ->
    SESet.fold
      (fun se acc ->
        let to_add = elaborate_lazy se in
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | App_p (e, []) when (not use_worklist) || Worklist.mem (Var e) prev_worklist
    ->
    SESet.fold
      (fun se acc ->
        let to_add = elaborate_lazy_p se in
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | Fld (e, fld) when (not use_worklist) || Worklist.mem (Var e) prev_worklist
    ->
    SESet.fold
      (fun se acc ->
        let to_add = elaborate_fld se fld in
        SESet.union to_add acc)
      (lookup_sc (Var e)) SESet.empty
  | Diff (e, p) when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    SESet.fold
      (fun se acc ->
        let filtered = filter_pat (se, p) in
        SESet.union filtered acc)
      (SESet.filter propagate (lookup_sc (Var e)))
      SESet.empty
  | Var e when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    SESet.filter propagate (lookup_sc (Var e))
  | Loc l when (not use_worklist) || Worklist.mem (Loc l) prev_worklist ->
    SESet.filter propagate (lookup_sc (Loc l))
  | _ -> SESet.empty

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
    SESet.iter
      (function
        | Ctor (_, l) -> (
          try
            let lhs = Loc (fst (List.nth l i)) in
            update_sc lhs set
          with _ -> ())
        | _ -> ())
      (lookup_sc (Var e))
  | _ -> failwith "Invalid LHS"

let step_sc () =
  if use_worklist then
    let to_be_reduced =
      SESet.fold
        (fun idx acc ->
          SESet.union
            (try Hashtbl.find reverse_sc idx with Not_found -> SESet.empty)
            acc)
        !prev_worklist SESet.empty
    in
    SESet.iter (fun x -> step_sc_for_entry x (lookup_sc x)) to_be_reduced
  else Hashtbl.iter step_sc_for_entry sc

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
