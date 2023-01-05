open SetExpression

let first = ref true

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
(* filter_pat (p, p') returns (p ∩ p', p - p') *)
let rec filter_pat = function
  | x, Top -> (GESet.singleton x, GESet.empty)
  | Top, x -> (GESet.singleton x, GESet.Total)
  | Loc (l, Immutable), p ->
    GESet.fold
      (fun y (acc_inter, acc_diff) ->
        let inter, diff = filter_pat (y, p) in
        (GESet.union inter acc_inter, GESet.union diff acc_diff))
      (try Hashtbl.find abs_mem l with _ -> GESet.empty)
      (GESet.empty, GESet.empty)
  | (Loc (_, Mutable) as x), _ -> (GESet.singleton x, GESet.singleton x)
  | x, p when x = p -> (GESet.singleton x, GESet.empty)
  | x, Const c when x <> Const c -> (GESet.empty, GESet.singleton x)
  | Const c, p when Const c <> p -> (GESet.empty, GESet.singleton (Const c))
  | Ctor_pat (kappa, l), Ctor_pat (kappa', l') ->
    if kappa <> kappa' || List.length l <> List.length l' then
      (GESet.empty, GESet.singleton (Ctor_pat (kappa, l)))
    else
      let inter, diff = filter_list ([[]], l) l' in
      ( GESet.of_list (List.map (fun l -> Ctor_pat (kappa, l)) inter),
        GESet.of_list (List.map (fun l -> Ctor_pat (kappa, l)) diff) )
  | _ -> assert false

and filter_list ((rev_hd : pattern se list list), tl) tl' =
  match (tl, tl') with
  | [], [] -> (List.map List.rev rev_hd, [])
  | hd :: tl1, hd' :: tl2 ->
    let inter, diff = filter_pat (hd, hd') in
    let new_rev_hd =
      GESet.fold (fun p acc -> List.map (fun l -> p :: l) rev_hd @ acc) inter []
    in
    let inter_total, diff_rest = filter_list (new_rev_hd, tl1) tl2 in
    let diff_total =
      GESet.fold
        (fun x acc ->
          List.map (fun rev -> List.rev_append rev (x :: tl1)) rev_hd @ acc)
        diff diff_rest
    in
    (inter_total, diff_total)
  | _ -> assert false

let filter_closure = function
  | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
  | App_V (Prim p, l) -> if p.prim_arity <> arg_len l then true else false
  | _ -> false

let allocated = Hashtbl.create 10

let value_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_V (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_V (x, [Some y]))
  | {CL.Primitive.prim_name = "%identity"}, [Some x] -> SESet.singleton x
  | {CL.Primitive.prim_name = "%ignore"}, [Some _] ->
    SESet.singleton (Ctor (Some "()", Static []))
  | {CL.Primitive.prim_name = "%field0"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 0)))
  | {CL.Primitive.prim_name = "%field1"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 1)))
  | {CL.Primitive.prim_name = "%setfield0"}, [Some x; Some y] ->
    update_c (Fld (x, (None, Some 0))) (SESet.singleton y) |> ignore;
    SESet.singleton (Ctor (Some "()", Static []))
  | {CL.Primitive.prim_name = "%makemutable"}, [Some x] -> (
    match Hashtbl.find allocated x with
    | exception Not_found ->
      Hashtbl.add allocated x ();
      let i =
        match x with
        | Var (Val (Expr_var (_, context))) -> new_memory context
        | Var (Val (Expr (_, context))) -> new_memory context
        | _ -> assert false
      in
      update_loc i (SESet.singleton x) |> ignore;
      SESet.singleton (Ctor (None, Static [(i, CL.Asttypes.Mutable)]))
    | _ -> SESet.empty)
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_V (x, []))
  | ( {
        CL.Primitive.prim_name =
          ( "%eq" | "%noteq" | "%ltint" | "%leint" | "%gtint" | "%geint"
          | "%eqfloat" | "%noteqfloat" | "%ltfloat" | "%lefloat" | "%gtfloat"
          | "%gefloat" | "%equal" | "%notequal" | "%lessequal" | "%lessthan"
          | "%greaterequal" | "%greaterthan" | "%compare" | "%boolnot"
          | "%sequand" | "%sequor" );
      },
      _ ) ->
    SESet.of_list
      [Ctor (Some "true", Static []); Ctor (Some "false", Static [])]
  | ( {
        CL.Primitive.prim_name =
          ( "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace"
          | "caml_sys_exit" );
      },
      _ ) ->
    SESet.empty
  | _ -> SESet.Total

let packet_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_P (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_P (x, [Some y]))
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_P (x, []))
  | {CL.Primitive.prim_name = "caml_sys_exit"}, _ ->
    SESet.singleton (Ctor (Some "Exit", Static []))
  | ( {
        CL.Primitive.prim_name =
          "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace";
      },
      Some x :: _ ) ->
    SESet.singleton x
  | _ -> SESet.empty

let time_spent_in_var = ref 0.0
let time_spent_in_filter = ref 0.0
let time_spent_in_fld = ref 0.0
let time_spent_in_closure = ref 0.0
let time_spent_in_update = ref 0.0
let time_spent_in_const = ref 0.0

let resolve_var var elt =
  match elt with
  | Top ->
    let t = Unix.gettimeofday () in
    update_g var GESet.Total |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Const c ->
    let t = Unix.gettimeofday () in
    update_g var (GESet.singleton (Const c)) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Ctor (kappa, Static l) when Worklist.mem (hash elt) prev_worklist ->
    let t = Unix.gettimeofday () in
    let l' = List.map (fun (loc, flag) -> Loc (loc, flag)) l in
    update_g var (GESet.singleton (Ctor_pat (kappa, l'))) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Ctor (None, Dynamic l) when Worklist.mem (hash elt) prev_worklist ->
    update_g var (GESet.singleton (Arr_pat l)) |> ignore
  | Var x when Worklist.mem (hash elt) prev_worklist ->
    let t = Unix.gettimeofday () in
    let c_set =
      SESet.filter filter_closure
        (try lookup_sc (Var x) with _ -> SESet.empty)
    in
    let g_set = try Hashtbl.find grammar x with Not_found -> GESet.empty in
    update_c (Var var) c_set |> ignore;
    update_g var g_set |> ignore;
    time_spent_in_var := !time_spent_in_var +. (Unix.gettimeofday () -. t)
  | App_V (Prim p, l) when Worklist.mem (hash (Prim p)) prev_worklist ->
    let t = Unix.gettimeofday () in
    if p.prim_arity = arg_len l then (
      let val_prim = value_prim (p, l) in
      update_c (Var var) val_prim |> ignore;
      if SESet.Total = val_prim then update_g var GESet.Total |> ignore);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_P (Prim p, l) when Worklist.mem (hash (Prim p)) prev_worklist ->
    let t = Unix.gettimeofday () in
    if p.prim_arity = arg_len l then
      update_c (Var var) (packet_prim (p, l)) |> ignore;
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_V (Var x, []) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Fn (None, l) ->
          let set = SESet.of_list (List.map (fun x -> Var (Val x)) l) in
          update_c (Var var) set |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_P (Var x, []) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Fn (None, l) ->
          let set = SESet.of_list (List.map (fun x -> Var (Packet x)) l) in
          update_c (Var var) set |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_V (Var x, Some (Var y) :: tl)
    when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Prim p ->
          update_c (Var var)
            (SESet.singleton (App_V (Prim p, Some (Var y) :: tl)))
          |> ignore
        | Fn (Some x, l) ->
          let values =
            if tl <> [] then
              SESet.of_list (List.map (fun e -> App_V (Var (Val e), tl)) l)
            else SESet.of_list (List.map (fun e -> Var (Val e)) l)
          in
          update_c (Var var) values |> ignore;
          update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y)) |> ignore
        | App_V (Prim p, l) when arg_len l < p.prim_arity ->
          let app =
            SESet.singleton (App_V (Prim p, merge_args (l, Some (Var y) :: tl)))
          in
          update_c (Var var) app |> ignore
        | App_V (f, None :: tl') ->
          let app =
            SESet.singleton (App_V (f, Some (Var y) :: merge_args (tl', tl)))
          in
          update_c (Var var) app |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_P (Var x, Some (Var y) :: tl)
    when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Prim p ->
          update_c (Var var)
            (SESet.singleton (App_P (Prim p, Some (Var y) :: tl)))
          |> ignore
        | Fn (Some x, l) ->
          let app_p =
            if tl <> [] then
              SESet.of_list (List.map (fun e -> App_P (Var (Val e), tl)) l)
            else SESet.empty
          in
          let body_p = SESet.of_list (List.map (fun e -> Var (Packet e)) l) in
          update_c (Var var) (SESet.union app_p body_p) |> ignore;
          update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y)) |> ignore
        | App_V (Prim p, l) when arg_len l < p.prim_arity ->
          let app =
            SESet.singleton (App_P (Prim p, merge_args (l, Some (Var y) :: tl)))
          in
          update_c (Var var) app |> ignore
        | App_V (f, None :: tl') ->
          let app =
            SESet.singleton (App_P (f, Some (Var y) :: merge_args (tl', tl)))
          in
          update_c (Var var) app |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | Fld (Var x, (None, Some i)) when Worklist.mem (hash (Var x)) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    GESet.iter
      (function
        | Top -> update_g var GESet.Total |> ignore
        | Ctor_pat (_, l) ->
          if i < List.length l then (
            let c_set =
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter filter_closure
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            in
            let g_set =
              match List.nth l i with
              | Loc (l, _) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            in
            update_c (Var var) c_set |> ignore;
            update_g var g_set |> ignore)
        | Arr_pat l ->
          let c_set =
            SESet.filter filter_closure
              (try lookup_mem l with _ -> SESet.empty)
          in
          let g_set = try Hashtbl.find abs_mem l with _ -> GESet.empty in
          update_c (Var var) c_set |> ignore;
          update_g var g_set |> ignore
        | _ -> ())
      (try Hashtbl.find grammar x with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Fld (Var x, (Some k, Some i)) when Worklist.mem (hash (Var x)) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    GESet.iter
      (function
        | Top -> update_g var GESet.Total |> ignore
        | Ctor_pat (Some k', l) when k = k' ->
          if i < List.length l then (
            let c_set =
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter filter_closure
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            in
            let g_set =
              match List.nth l i with
              | Loc (l, _) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            in
            update_c (Var var) c_set |> ignore;
            update_g var g_set |> ignore)
        | _ -> ())
      (try Hashtbl.find grammar x with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Diff (Var x, p) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    let () =
      if !Common.Cli.debug_pat then (
        PrintSE.print_tagged_expr x;
        prerr_newline ())
    in
    let filtered =
      GESet.fold
        (fun y acc_diff ->
          let _, diff = filter_pat (y, p) in
          let widened_diff =
            if GESet.is_empty diff then GESet.empty else GESet.singleton y
          in
          GESet.union widened_diff acc_diff)
        (try Hashtbl.find grammar x with _ -> GESet.empty)
        GESet.empty
    in
    update_g var filtered |> ignore;
    time_spent_in_filter := !time_spent_in_filter +. (Unix.gettimeofday () -. t)
  | _ -> ()

let resolve_update (var, i) set =
  match Hashtbl.find grammar var with
  | p_set ->
    GESet.iter
      (function
        | Ctor_pat (None, l) -> (
          if i < List.length l then
            match List.nth l i with
            | Loc (l, Mutable) -> update_loc l set |> ignore
            | _ -> ())
        | Arr_pat l -> update_loc l set |> ignore
        | _ -> ())
      p_set
  | exception Not_found -> ()

let step_sc_for_entry x set =
  match x with
  | Var var -> SESet.iter (resolve_var var) set
  | Fld (Var var, (None, Some i)) ->
    let t = Unix.gettimeofday () in
    resolve_update (var, i) set;
    time_spent_in_update := !time_spent_in_update +. (Unix.gettimeofday () -. t)
  | _ -> ()

let step_sc_for_file tbl = Hashtbl.iter step_sc_for_entry tbl

let step_sc added_file =
  if not !first then
    let to_be_reduced =
      Seq.fold_left
        (fun acc (idx, ()) ->
          SESet.union
            (try Hashtbl.find reverse_sc idx with Not_found -> SESet.empty)
            acc)
        SESet.empty
        (Hashtbl.to_seq prev_worklist)
    in
    SESet.iter
      (fun x ->
        step_sc_for_entry x (try lookup_sc x with Not_found -> SESet.empty))
      to_be_reduced
  else try step_sc_for_file (Hashtbl.find sc added_file) with Not_found -> ()

let resolve_mem loc elt =
  match elt with
  | Top ->
    let t = Unix.gettimeofday () in
    update_abs_loc loc GESet.Total |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Const c ->
    let t = Unix.gettimeofday () in
    update_abs_loc loc (GESet.singleton (Const c)) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Ctor (kappa, Static l) when Worklist.mem (hash elt) prev_worklist ->
    let t = Unix.gettimeofday () in
    let l' = List.map (fun (loc, flag) -> Loc (loc, flag)) l in
    update_abs_loc loc (GESet.singleton (Ctor_pat (kappa, l'))) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Ctor (None, Dynamic l) when Worklist.mem (hash elt) prev_worklist ->
    update_abs_loc loc (GESet.singleton (Arr_pat l)) |> ignore
  | Var x when Worklist.mem (hash elt) prev_worklist ->
    let t = Unix.gettimeofday () in
    let c_set =
      SESet.filter filter_closure
        (try lookup_sc (Var x) with _ -> SESet.empty)
    in
    let g_set = try Hashtbl.find grammar x with Not_found -> GESet.empty in
    update_loc loc c_set |> ignore;
    update_abs_loc loc g_set |> ignore;
    time_spent_in_var := !time_spent_in_var +. (Unix.gettimeofday () -. t)
  | App_V (Prim p, l) when Worklist.mem (hash (Prim p)) prev_worklist ->
    let t = Unix.gettimeofday () in
    if p.prim_arity = arg_len l then (
      let val_prim = value_prim (p, l) in
      update_loc loc val_prim |> ignore;
      if val_prim = SESet.Total then update_abs_loc loc GESet.Total |> ignore);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_P (Prim p, l) when Worklist.mem (hash (Prim p)) prev_worklist ->
    let t = Unix.gettimeofday () in
    if p.prim_arity = arg_len l then
      update_loc loc (packet_prim (p, l)) |> ignore;
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_V (Var x, []) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Fn (None, l) ->
          let set = SESet.of_list (List.map (fun x -> Var (Val x)) l) in
          update_loc loc set |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_P (Var x, []) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Fn (None, l) ->
          let set = SESet.of_list (List.map (fun x -> Var (Packet x)) l) in
          update_loc loc set |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_V (Var x, Some (Var y) :: tl)
    when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Prim p ->
          update_loc loc (SESet.singleton (App_V (Prim p, Some (Var y) :: tl)))
          |> ignore
        | Fn (Some x, l) ->
          let values =
            if tl <> [] then
              SESet.of_list (List.map (fun e -> App_V (Var (Val e), tl)) l)
            else SESet.of_list (List.map (fun e -> Var (Val e)) l)
          in
          update_loc loc values |> ignore;
          update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y)) |> ignore
        | App_V (Prim p, l) when arg_len l < p.prim_arity ->
          let app =
            SESet.singleton (App_V (Prim p, merge_args (l, Some (Var y) :: tl)))
          in
          update_loc loc app |> ignore
        | App_V (f, None :: tl') ->
          let app =
            SESet.singleton (App_V (f, Some (Var y) :: merge_args (tl', tl)))
          in
          update_loc loc app |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | App_P (Var x, Some (Var y) :: tl)
    when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    SESet.iter
      (function
        | Prim p ->
          update_loc loc (SESet.singleton (App_P (Prim p, Some (Var y) :: tl)))
          |> ignore
        | Fn (Some x, l) ->
          let app_p =
            if tl <> [] then
              SESet.of_list (List.map (fun e -> App_P (Var (Val e), tl)) l)
            else SESet.empty
          in
          let body_p = SESet.of_list (List.map (fun e -> Var (Packet e)) l) in
          update_loc loc (SESet.union app_p body_p) |> ignore;
          update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y)) |> ignore
        | App_V (Prim p, l) ->
          let app =
            SESet.singleton (App_P (Prim p, merge_args (l, Some (Var y) :: tl)))
          in
          update_loc loc app |> ignore
        | App_V (f, None :: tl') ->
          let app =
            SESet.singleton (App_P (f, Some (Var y) :: merge_args (tl', tl)))
          in
          update_loc loc app |> ignore
        | _ -> ())
      (try lookup_sc (Var x) with _ -> SESet.empty);
    time_spent_in_closure :=
      !time_spent_in_closure +. (Unix.gettimeofday () -. t)
  | Fld (Var x, (None, Some i)) when Worklist.mem (hash (Var x)) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    GESet.iter
      (function
        | Top -> update_abs_loc loc GESet.Total |> ignore
        | Ctor_pat (_, l) ->
          if i < List.length l then (
            let c_set =
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter filter_closure
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            in
            let g_set =
              match List.nth l i with
              | Loc (l, _) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            in
            update_loc loc c_set |> ignore;
            update_abs_loc loc g_set |> ignore)
        | Arr_pat l ->
          let c_set =
            SESet.filter filter_closure
              (try lookup_mem l with _ -> SESet.empty)
          in
          let g_set = try Hashtbl.find abs_mem l with _ -> GESet.empty in
          update_loc loc c_set |> ignore;
          update_abs_loc loc g_set |> ignore
        | _ -> ())
      (try Hashtbl.find grammar x with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Fld (Var x, (Some k, Some i)) when Worklist.mem (hash (Var x)) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    GESet.iter
      (function
        | Top -> update_abs_loc loc GESet.Total |> ignore
        | Ctor_pat (Some k', l) when k = k' ->
          if i < List.length l then (
            let c_set =
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter filter_closure
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            in
            let g_set =
              match List.nth l i with
              | Loc (l, _) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            in
            update_loc loc c_set |> ignore;
            update_abs_loc loc g_set |> ignore)
        | _ -> ())
      (try Hashtbl.find grammar x with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Diff (Var x, p) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    let filtered =
      GESet.fold
        (fun y acc_diff ->
          let _, diff = filter_pat (y, p) in
          let widened_diff =
            if GESet.is_empty diff then GESet.empty else GESet.singleton y
          in
          GESet.union widened_diff acc_diff)
        (try Hashtbl.find grammar x with _ -> GESet.empty)
        GESet.empty
    in
    update_abs_loc loc filtered |> ignore;
    time_spent_in_filter := !time_spent_in_filter +. (Unix.gettimeofday () -. t)
  | _ -> ()

let step_mem_for_file tbl =
  Hashtbl.iter (fun loc set -> SESet.iter (resolve_mem loc) set) tbl

let step_mem added_file =
  if not !first then
    let to_be_reduced =
      Seq.fold_left
        (fun acc (idx, ()) ->
          LocSet.union
            (try Hashtbl.find reverse_mem idx with Not_found -> LocSet.empty)
            acc)
        LocSet.empty
        (Hashtbl.to_seq prev_worklist)
    in
    LocSet.iter
      (fun x ->
        SESet.iter (resolve_mem x)
          (try lookup_mem x with Not_found -> SESet.empty))
      to_be_reduced
  else
    try step_mem_for_file (Hashtbl.find memory added_file)
    with Not_found -> ()

let prepare_step () =
  changed := false;
  Worklist.prepare_step worklist prev_worklist

let solve added_file =
  Format.flush_str_formatter () |> ignore;
  prepare_step ();
  if not !linking then first := true;
  step_sc added_file;
  step_mem added_file;
  if not !linking then first := false;
  while !changed do
    prepare_step ();
    step_sc added_file;
    step_mem added_file
  done
