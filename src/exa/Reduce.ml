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
    update_sc
      (Fld (x, (None, Some 0)))
      (Cstr.add env (SESet.singleton (Var y)) Cstr.empty);
    SESet.singleton (Ctor (Some "()", []))
  | {CL.Primitive.prim_name = "%makemutable"}, [Some x] -> (
    let value = Cstr.add env (SESet.singleton (Var x)) Cstr.empty in
    match Hashtbl.find allocated x with
    | exception Not_found ->
      let i = new_memory (get_context (Var x)) in
      Hashtbl.add allocated x i;
      update_sc (Loc i) value;
      SESet.singleton (Ctor (None, [i]))
    | i ->
      update_sc (Loc i) value;
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

let elaborate_app env f hd tl =
  match f with
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let value = SESet.singleton (App_v (bound, Some hd :: tl)) in
      Cstr.add env value Cstr.empty
    with Not_found -> Cstr.empty)
  | Fn (Some x, body) ->
    let value =
      SESet.of_list
        (List.map
           (fun loc -> if tl = [] then Var (Val loc) else App_v (Val loc, tl))
           body)
    in
    let bound = lookup_id x in
    let updated_key = SEnv.Internal.update x (fun _ -> Some hd) env in
    update_sc (Var bound)
      (Cstr.add updated_key (SESet.singleton (Var hd)) Cstr.empty);
    Cstr.add updated_key value Cstr.empty
  | Prim p ->
    let args = Some hd :: tl in
    let value =
      if arg_len args = p.prim_arity then value_prim env (p, args)
      else SESet.singleton (Prim_v (p, args))
    in
    Cstr.add env value Cstr.empty
  | App_v (e, None :: tl') ->
    let value = SESet.singleton (App_v (e, Some hd :: merge_args (tl', tl))) in
    Cstr.add env value Cstr.empty
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    let value =
      if arg_len args = p.prim_arity then value_prim env (p, args)
      else SESet.singleton (Prim_v (p, args))
    in
    Cstr.add env value Cstr.empty
  | _ -> Cstr.empty

let elaborate_app_p env f hd tl =
  match f with
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let packet = SESet.singleton (App_p (bound, Some hd :: tl)) in
      Cstr.add env packet Cstr.empty
    with Not_found -> Cstr.empty)
  | Fn (Some x, body) ->
    let app =
      if tl = [] then SESet.empty
      else SESet.of_list (List.map (fun e -> App_p (Val e, tl)) body)
    in
    let body = SESet.of_list (List.map (fun e -> Var (Packet e)) body) in
    let packet = SESet.union body app in
    let bound = lookup_id x in
    let updated_key = SEnv.Internal.update x (fun _ -> Some hd) env in
    update_sc (Var bound)
      (Cstr.add updated_key (SESet.singleton (Var hd)) Cstr.empty);
    Cstr.add updated_key packet Cstr.empty
  | Prim p ->
    let args = Some hd :: tl in
    let packet =
      if arg_len args = p.prim_arity then packet_prim (p, args) else SESet.empty
    in
    Cstr.add env packet Cstr.empty
  | App_v (e, None :: tl') ->
    let packet = SESet.singleton (App_p (e, Some hd :: merge_args (tl', tl))) in
    Cstr.add env packet Cstr.empty
  | Prim_v (p, args) when arg_len args < p.prim_arity ->
    let args = merge_args (args, Some hd :: tl) in
    let packet =
      if arg_len args = p.prim_arity then packet_prim (p, args) else SESet.empty
    in
    Cstr.add env packet Cstr.empty
  | _ -> Cstr.empty

let elaborate_lazy f =
  match f with
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let value = SESet.singleton (App_v (bound, [])) in
      value
    with Not_found -> SESet.empty)
  | Fn (None, body) ->
    let value = SESet.of_list (List.map (fun loc -> Var (Val loc)) body) in
    value
  | _ -> SESet.empty

let elaborate_lazy_p f =
  match f with
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let packet = SESet.singleton (App_p (bound, [])) in
      packet
    with Not_found -> SESet.empty)
  | Fn (None, body) ->
    let packet = SESet.of_list (List.map (fun loc -> Var (Packet loc)) body) in
    packet
  | _ -> SESet.empty

let elaborate_fld se fld =
  match se with
  | Top -> SESet.singleton Top
  | Id (x, ctx) -> (
    try
      let bound = lookup_id (x, ctx) in
      let value = SESet.singleton (Fld (bound, fld)) in
      value
    with Not_found -> SESet.empty)
  | Ctor (kappa, l) -> (
    match fld with
    | None, Some i -> (
      try SESet.singleton (Loc (List.nth l i)) with _ -> SESet.empty)
    | Some k, Some i -> (
      try
        if kappa = Some k then SESet.singleton (Loc (List.nth l i))
        else SESet.empty
      with _ -> SESet.empty)
    | _ -> SESet.empty)
  | Arr l -> SESet.singleton (Loc l)
  | _ -> SESet.empty

let filter = function
  | Top | Const _ | Ctor _ | Arr _ | Prim _ | Fn _
  | App_v (_, None :: _)
  | App_p (_, None :: _)
  | Prim_v _ | Prim_p _ | Id _ ->
    true
  | _ -> false

let filter_pat = function
  | _, Top -> SESet.empty
  | Id x, p -> (
    try
      let bound = lookup_id x in
      SESet.singleton (Diff (bound, p))
    with Not_found -> SESet.empty)
  | Ctor (k, l), Ctor_pat (k', l') ->
    if k = k' && List.length l = List.length l' then
      if List.fold_left (fun acc p -> acc && p = Top) true l' then SESet.empty
      else SESet.singleton (Ctor (k, l))
    else SESet.singleton (Ctor (k, l))
  | Const c, Const c' ->
    if c = c' then SESet.empty else SESet.singleton (Const c)
  | x, _ -> if filter x then SESet.singleton x else SESet.empty

let use_worklist = true

(** given a collection of set expressions under env, elaborate upon possible expressions *)
let elaborate env se =
  match se with
  | Top | Const _ | Ctor _ | Arr _ | Prim _ | Fn _
  | App_v (_, None :: _)
  | App_p (_, None :: _)
  | Prim_v _ | Prim_p _ | Id _ ->
    Cstr.empty
  | App_v (e, Some e' :: tl)
    when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let elaborated =
            SESet.fold
              (fun se acc ->
                let to_add = elaborate_app key se e' tl in
                cstr_union to_add acc)
              set Cstr.empty
          in
          cstr_union elaborated acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Var e)) Cstr.empty
  | App_p (e, Some e' :: tl)
    when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let elaborated =
            SESet.fold
              (fun se acc ->
                let to_add = elaborate_app_p key se e' tl in
                cstr_union to_add acc)
              set Cstr.empty
          in
          cstr_union elaborated acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Var e)) Cstr.empty
  | App_v (e, []) when (not use_worklist) || Worklist.mem (Var e) prev_worklist
    ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let elaborated =
            SESet.fold
              (fun se acc ->
                let to_add = elaborate_lazy se in
                SESet.union acc to_add)
              set SESet.empty
          in
          Cstr.update key
            (function
              | None -> Some elaborated
              | Some x -> Some (SESet.union x elaborated))
            acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Var e)) Cstr.empty
  | App_p (e, []) when (not use_worklist) || Worklist.mem (Var e) prev_worklist
    ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let elaborated =
            SESet.fold
              (fun se acc ->
                let to_add = elaborate_lazy_p se in
                SESet.union acc to_add)
              set SESet.empty
          in
          Cstr.update key
            (function
              | None -> Some elaborated
              | Some x -> Some (SESet.union x elaborated))
            acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Var e)) Cstr.empty
  | Fld (e, fld) when (not use_worklist) || Worklist.mem (Var e) prev_worklist
    ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let elaborated =
            SESet.fold
              (fun se acc ->
                let to_add = elaborate_fld se fld in
                SESet.union acc to_add)
              set SESet.empty
          in
          Cstr.update key
            (function
              | None -> Some elaborated
              | Some x -> Some (SESet.union x elaborated))
            acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Var e)) Cstr.empty
  | Diff (e, p) when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let filtered =
            SESet.fold
              (fun se acc ->
                let filtered = filter_pat (se, p) in
                SESet.union filtered acc)
              set SESet.empty
          in
          Cstr.update key
            (function
              | None -> Some filtered | Some x -> Some (SESet.union x filtered))
            acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Var e)) Cstr.empty
  | Var e when (not use_worklist) || Worklist.mem (Var e) prev_worklist ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let filtered = SESet.filter filter set in
          Cstr.update key
            (function
              | None -> Some filtered | Some x -> Some (SESet.union x filtered))
            acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Var e)) Cstr.empty
  | Loc l when (not use_worklist) || Worklist.mem (Loc l) prev_worklist ->
    Cstr.fold
      (fun env' set acc ->
        try
          let key = SEnv.union env env' in
          let filtered = SESet.filter filter set in
          Cstr.update key
            (function
              | None -> Some filtered | Some x -> Some (SESet.union x filtered))
            acc
        with SEnv.Inconsistent -> acc)
      (lookup_sc (Loc l)) Cstr.empty
  | _ -> Cstr.empty

let step_sc_for_entry x cstr =
  match x with
  | Var _ | Loc _ ->
    let elaborated =
      Cstr.fold
        (fun env set acc ->
          let elaborated =
            SESet.fold
              (fun se acc ->
                let elaborated = elaborate env se in
                cstr_union elaborated acc)
              set Cstr.empty
          in
          cstr_union elaborated acc)
        cstr Cstr.empty
    in
    update_sc x elaborated
  | Fld (e, (None, Some i)) ->
    Cstr.iter
      (fun env ->
        let rhs =
          Cstr.fold
            (fun env' set acc ->
              try
                let key = SEnv.union env env' in
                Cstr.add key set acc
              with SEnv.Inconsistent -> acc)
            cstr Cstr.empty
        in
        SESet.iter (function
          | Id x -> (
            try
              let lhs = lookup_id x in
              update_sc (Fld (lhs, (None, Some i))) rhs
            with Not_found -> ())
          | Ctor (_, l) -> (
            try
              let lhs = Loc (List.nth l i) in
              update_sc lhs rhs
            with _ -> ())
          | _ -> ()))
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
