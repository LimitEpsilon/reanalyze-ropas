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

let value_prim env = function
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
    update_sc env (Fld (x, (None, Some 0))) (SESet.singleton (Var y));
    SESet.singleton (Ctor (Some "()", []))
  | {CL.Primitive.prim_name = "%makemutable"}, [Some x] -> (
    let value = SESet.singleton (Var x) in
    match Hashtbl.find allocated x with
    | exception Not_found ->
      let i = new_memory (get_context (Var x)) in
      Hashtbl.add allocated x i;
      update_sc env (Loc i) value;
      SESet.singleton (Ctor (None, [i]))
    | i ->
      update_sc env (Loc i) value;
      SESet.singleton (Ctor (None, [i])))
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

let elaborate_app env lhs hd tl = function
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let value = SESet.singleton (App_v (bound, Some hd :: tl)) in
      update_sc env lhs value
    with Not_found -> ())
  | Fn (Some x, body) ->
    let value =
      SESet.of_list
        (List.map
           (fun loc -> if tl = [] then Var (Val loc) else App_v (Val loc, tl))
           body)
    in
    let bound = lookup_id x in
    let updated_key = SEnv.Internal.update x (fun _ -> Some hd) env in
    update_sc updated_key (Var bound) (SESet.singleton (Var hd));
    update_sc updated_key lhs value
  | Prim p ->
    let args = Some hd :: tl in
    let value =
      if arg_len args = p.prim_arity then value_prim env (p, args)
      else SESet.singleton (Prim_v (p, args))
    in
    update_sc env lhs value
  | App_v (e, None :: tl') ->
    let value = SESet.singleton (App_v (e, Some hd :: merge_args (tl', tl))) in
    update_sc env lhs value
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    let value =
      if arg_len args = p.prim_arity then value_prim env (p, args)
      else SESet.singleton (Prim_v (p, args))
    in
    update_sc env lhs value
  | _ -> ()

let elaborate_app_p env lhs hd tl = function
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let packet = SESet.singleton (App_p (bound, Some hd :: tl)) in
      update_sc env lhs packet
    with Not_found -> ())
  | Fn (Some x, body) ->
    let app =
      if tl = [] then SESet.empty
      else SESet.of_list (List.map (fun e -> App_p (Val e, tl)) body)
    in
    let body = SESet.of_list (List.map (fun e -> Var (Packet e)) body) in
    let packet = SESet.union body app in
    let bound = lookup_id x in
    let updated_key = SEnv.Internal.update x (fun _ -> Some hd) env in
    update_sc updated_key (Var bound) (SESet.singleton (Var hd));
    update_sc updated_key lhs packet
  | Prim p ->
    let args = Some hd :: tl in
    let packet =
      if arg_len args = p.prim_arity then packet_prim (p, args) else SESet.empty
    in
    update_sc env lhs packet
  | App_v (e, None :: tl') ->
    let packet = SESet.singleton (App_p (e, Some hd :: merge_args (tl', tl))) in
    update_sc env lhs packet
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    let packet =
      if arg_len args = p.prim_arity then packet_prim (p, args) else SESet.empty
    in
    update_sc env lhs packet
  | _ -> ()

let elaborate_lazy env lhs = function
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let value = SESet.singleton (App_v (bound, [])) in
      update_sc env lhs value
    with Not_found -> ())
  | Fn (None, body) ->
    let value = SESet.of_list (List.map (fun loc -> Var (Val loc)) body) in
    update_sc env lhs value
  | _ -> ()

let elaborate_lazy_p env lhs = function
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let packet = SESet.singleton (App_p (bound, [])) in
      update_sc env lhs packet
    with Not_found -> ())
  | Fn (None, body) ->
    let packet = SESet.of_list (List.map (fun loc -> Var (Packet loc)) body) in
    update_sc env lhs packet
  | _ -> ()

let elaborate_fld env lhs fld = function
  | Top -> update_sc env lhs (SESet.singleton Top)
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let value = SESet.singleton (Fld (bound, fld)) in
      update_sc env lhs value
    with Not_found -> ())
  | Ctor (kappa, l) ->
    let value =
      match fld with
      | None, Some i -> (
        try SESet.singleton (Loc (List.nth l i)) with _ -> SESet.empty)
      | Some k, Some i -> (
        try
          if kappa = Some k then SESet.singleton (Loc (List.nth l i))
          else SESet.empty
        with _ -> SESet.empty)
      | _ -> SESet.empty
    in
    update_sc env lhs value
  | Arr l -> update_sc env lhs (SESet.singleton (Loc l))
  | _ -> ()

let filter = function
  | Top | Const _ | Ctor _ | Arr _ | Prim _ | Fn _
  | App_v (_, None :: _)
  | App_p (_, None :: _)
  | Prim_v _ | Prim_p _ | Id _ ->
    true
  | _ -> false

let filter_pat env lhs = function
  | _, Top -> ()
  | Id x, p -> (
    try
      let bound = lookup_id x in
      let value = SESet.singleton (Diff (bound, p)) in
      update_sc env lhs value
    with Not_found -> ())
  | Ctor (k, l), Ctor_pat (k', l') ->
    let value =
      if k = k' && List.length l = List.length l' then
        if List.fold_left (fun acc p -> acc && p = Top) true l' then SESet.empty
        else SESet.singleton (Ctor (k, l))
      else SESet.singleton (Ctor (k, l))
    in
    update_sc env lhs value
  | Const c, Const c' ->
    let value = if c = c' then SESet.empty else SESet.singleton (Const c) in
    update_sc env lhs value
  | x, _ ->
    let value = if filter x then SESet.singleton x else SESet.empty in
    update_sc env lhs value

(** given a collection of set expressions under env, elaborate upon possible expressions *)
let elaborate env lhs = function
  | Top | Const _ | Ctor _ | Arr _ | Prim _ | Fn _
  | App_v (_, None :: _)
  | App_p (_, None :: _)
  | Prim_v _ | Prim_p _ | Id _ ->
    ()
  | App_v (e, Some e' :: tl) when Worklist.mem (Var e) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set = Hashtbl.find (Cstr.find env' !sc) (Var e) in
          SESet.iter (elaborate_app merged lhs e' tl) set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | App_p (e, Some e' :: tl) when Worklist.mem (Var e) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set = Hashtbl.find (Cstr.find env' !sc) (Var e) in
          SESet.iter (elaborate_app_p merged lhs e' tl) set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | App_v (e, []) when Worklist.mem (Var e) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set = Hashtbl.find (Cstr.find env' !sc) (Var e) in
          SESet.iter (elaborate_lazy merged lhs) set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | App_p (e, []) when Worklist.mem (Var e) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set = Hashtbl.find (Cstr.find env' !sc) (Var e) in
          SESet.iter (elaborate_lazy_p merged lhs) set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | Fld (e, fld) when Worklist.mem (Var e) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set = Hashtbl.find (Cstr.find env' !sc) (Var e) in
          SESet.iter (elaborate_fld merged lhs fld) set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | Diff (e, p) when Worklist.mem (Var e) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set = Hashtbl.find (Cstr.find env' !sc) (Var e) in
          SESet.iter (fun e -> filter_pat merged lhs (e, p)) set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | Var e when Worklist.mem (Var e) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set =
            SESet.filter filter (Hashtbl.find (Cstr.find env' !sc) (Var e))
          in
          update_sc merged lhs set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | Loc l when Worklist.mem (Loc l) prev_worklist ->
    let envs_to_lookup =
      try Hashtbl.find environments (Loc l) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set =
            SESet.filter filter (Hashtbl.find (Cstr.find env' !sc) (Loc l))
          in
          update_sc merged lhs set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | _ -> ()

let for_each_constraint env lhs rhs =
  match lhs with
  | Var _ | Loc _ -> SESet.iter (elaborate env lhs) rhs
  | Fld (e, (None, Some i)) ->
    let envs_to_lookup =
      try Hashtbl.find environments (Var e) with Not_found -> SEnvSet.empty
    in
    SEnvSet.iter
      (fun env' ->
        try
          let merged = SEnv.union env env' in
          let set = Hashtbl.find (Cstr.find env' !sc) (Var e) in
          SESet.iter
            (function
              | Id x -> (
                try
                  let lhs = lookup_id x in
                  update_sc merged (Fld (lhs, (None, Some i))) rhs
                with Not_found -> ())
              | Ctor (_, l) -> (
                try
                  let lhs = Loc (List.nth l i) in
                  update_sc merged lhs rhs
                with _ -> ())
              | _ -> ())
            set
        with SEnv.Inconsistent -> ())
      envs_to_lookup
  | _ -> failwith "Invalid LHS"

let one_step worklist_with_context env tbl =
  let to_elaborate =
    try Cstr.find env worklist_with_context with Not_found -> SESet.empty
  in
  SESet.iter
    (fun lhs ->
      let rhs = lookup_sc tbl lhs in
      for_each_constraint env lhs rhs)
    to_elaborate

let step_sc () =
  let worklist_with_context =
    Cstr.map
      (fun tbl ->
        SESet.fold
          (fun se acc ->
            let set = try Hashtbl.find tbl se with Not_found -> SESet.empty in
            SESet.union set acc)
          !prev_worklist SESet.empty)
      !reverse_sc
  in
  Cstr.iter (one_step worklist_with_context) !sc

let num_of_iters = ref 0

let prepare_step () =
  incr num_of_iters;
  prerr_endline ("Iteration #" ^ string_of_int !num_of_iters);
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
