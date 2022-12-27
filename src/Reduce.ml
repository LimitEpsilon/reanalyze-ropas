open SetExpression
open PrintSE

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

(* no support for arrays yet *)
let rec filter_pat = function
  | _, Top -> GESet.empty
  | Var x, p ->
    GESet.fold
      (fun y acc -> GESet.union (filter_pat (y, p)) acc)
      (try Hashtbl.find grammar (Var x) with _ -> GESet.empty)
      GESet.empty
  | Loc (l, None), p ->
    GESet.map
      (fun x -> Loc (l, Some x))
      (GESet.fold
         (fun y acc -> GESet.union (filter_pat (y, p)) acc)
         (try Hashtbl.find abs_mem l with _ -> GESet.empty)
         GESet.empty)
  | Loc (l, Some p), p' ->
    GESet.map (fun x -> Loc (l, Some x)) (filter_pat (p, p'))
  | x, p when x = p -> GESet.empty
  | x, Const c -> if x <> Const c then GESet.singleton x else GESet.empty
  | Top, Ctor_pat (kappa, l) ->
    filter_pat (Ctor_pat (kappa, List.map (fun _ -> Top) l), Ctor_pat (kappa, l))
  | Ctor_pat (kappa, l), Ctor_pat (kappa', l') ->
    if kappa <> kappa' || List.length l <> List.length l' then
      GESet.singleton (Ctor_pat (kappa, l))
    else
      let filtered_lists =
        List.map (fun l -> Ctor_pat (kappa, l)) (diff_list ([], l) l')
      in
      GESet.of_list filtered_lists
  | x, _ -> GESet.singleton x

and diff_list (rev_hd, tl) tl' =
  match (tl, tl') with
  | [], _ -> []
  | hd :: tl1, hd' :: tl2 ->
    let set = filter_pat (hd, hd') in
    let diff_rest = diff_list (hd :: rev_hd, tl1) tl2 in
    GESet.fold
      (fun x acc -> List.rev_append rev_hd (x :: tl1) :: acc)
      set diff_rest
  | _ -> []

let rec filter_pat_debug (x, y) =
  prerr_string "\t";
  print_pattern x;
  prerr_newline ();
  prerr_string "\t";
  print_pattern y;
  prerr_newline ();
  prerr_string "\t\t";
  match (x, y) with
  | _, Top ->
    prerr_endline "rhs = Top";
    GESet.empty
  | Var x, p ->
    prerr_endline "lhs = var";
    GESet.fold
      (fun y acc -> GESet.union (filter_pat_debug (y, p)) acc)
      (try Hashtbl.find grammar (Var x) with _ -> GESet.empty)
      GESet.empty
  | Loc (l, None), p ->
    prerr_endline "lhs = loc";
    GESet.map
      (fun x -> Loc (l, Some x))
      (GESet.fold
         (fun y acc -> GESet.union (filter_pat_debug (y, p)) acc)
         (try Hashtbl.find abs_mem l with _ -> GESet.empty)
         GESet.empty)
  | Loc (l, Some p), p' ->
    prerr_endline "lhs = loc with pat";
    GESet.map (fun x -> Loc (l, Some x)) (filter_pat_debug (p, p'))
  | x, p when x = p ->
    prerr_endline "lhs = rhs";
    GESet.empty
  | x, Const c ->
    prerr_endline "rhs = const";
    if x <> Const c then GESet.singleton x else GESet.empty
  | Top, Ctor_pat (kappa, arr) ->
    prerr_endline "lhs = Top, rhs = Ctor, coerce Top into Ctor";
    filter_pat_debug
      (Ctor_pat (kappa, List.map (fun _ -> Top) arr), Ctor_pat (kappa, arr))
  | Ctor_pat (kappa, l), Ctor_pat (kappa', l') ->
    prerr_endline "lhs, rhs = Ctor";
    if kappa <> kappa' || List.length l <> List.length l' then
      GESet.singleton (Ctor_pat (kappa, l))
    else
      let filtered_lists =
        List.map (fun l -> Ctor_pat (kappa, l)) (diff_list ([], l) l')
      in
      GESet.of_list filtered_lists
  | x, _ ->
    prerr_endline "else";
    GESet.singleton x

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
      SESet.singleton (Ctor (None, Static [i]))
    | _ -> SESet.empty)
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_V (x, []))
  | _ -> SESet.singleton Top

let packet_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_P (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_P (x, [Some y]))
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_P (x, []))
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
    update_g var (GESet.singleton Top) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Const c when !first ->
    let t = Unix.gettimeofday () in
    update_g var (GESet.singleton (Const c)) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Ctor (kappa, Static l) when !first || Worklist.mem (hash elt) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    let l' = List.map (fun i -> Loc (i, None)) l in
    update_g var (GESet.singleton (Ctor_pat (kappa, l'))) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Var x when Worklist.mem (hash elt) prev_worklist ->
    let t = Unix.gettimeofday () in
    let set =
      SESet.filter
        (function
          | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
          | App_V (Prim p, l) ->
            if arg_len l < p.prim_arity then true else false
          | _ -> false)
        (try lookup_sc (Var x) with _ -> SESet.empty)
    in
    update_c (Var var) set |> ignore;
    if Hashtbl.mem grammar (Var x) then
      update_g var (Hashtbl.find grammar (Var x)) |> ignore;
    time_spent_in_var := !time_spent_in_var +. (Unix.gettimeofday () -. t)
  | App_V (Prim p, l) when Worklist.mem (hash (Prim p)) prev_worklist ->
    let t = Unix.gettimeofday () in
    if p.prim_arity = arg_len l then
      update_c (Var var) (value_prim (p, l)) |> ignore;
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
        | Top -> update_g var (GESet.singleton Top) |> ignore
        | Ctor_pat (_, l) ->
          let c_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter
                  (function
                    | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                    | App_V (Prim p, l) ->
                      if p.prim_arity <> arg_len l then true else false
                    | _ -> false)
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            else SESet.empty
          in
          let g_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (_, Some p) -> GESet.singleton p
              | Loc (l, None) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            else GESet.empty
          in
          update_c (Var var) c_set |> ignore;
          update_g var g_set |> ignore
        | _ -> ())
      (try Hashtbl.find grammar (Var x) with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Fld (Var x, (Some k, Some i)) when Worklist.mem (hash (Var x)) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    GESet.iter
      (function
        | Top -> update_g var (GESet.singleton Top) |> ignore
        | Ctor_pat (Some k', l) when k = k' ->
          let c_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter
                  (function
                    | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                    | App_V (Prim p, l) ->
                      if p.prim_arity <> arg_len l then true else false
                    | _ -> false)
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            else SESet.empty
          in
          let g_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (_, Some p) -> GESet.singleton p
              | Loc (l, None) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            else GESet.empty
          in
          update_c (Var var) c_set |> ignore;
          update_g var g_set |> ignore
        | _ -> ())
      (try Hashtbl.find grammar (Var x) with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Diff (Var x, p) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    if !Common.Cli.debug_pat then (
      (match x with
      | Val (Expr_var (x, _)) -> prerr_endline (CL.Ident.name x)
      | _ -> ());
      update_g var (filter_pat_debug (Var x, p)) |> ignore)
    else update_g var (filter_pat (Var x, p)) |> ignore;
    time_spent_in_filter := !time_spent_in_filter +. (Unix.gettimeofday () -. t)
  | _ -> ()

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
    (function Var x -> fun () -> update_g x set |> ignore | _ -> fun () -> ())
    back_propagated_vars

let resolve_update (var, i) set =
  match Hashtbl.find grammar (Var var) with
  | p_set ->
    GESet.iter
      (function
        | Ctor_pat (k, l) -> (
          if i < List.length l then
            match List.nth l i with
            | Loc (loc, Some _) ->
              let j = ref (-1) in
              let temp =
                List.fold_left
                  (fun acc x ->
                    incr j;
                    if !j = i then Loc (loc, None) :: acc else x :: acc)
                  [] l
              in
              let temp_pat = Ctor_pat (k, List.rev temp) in
              if GESet.mem temp_pat p_set then ()
              else (
                update_loc loc set |> ignore;
                back_propagate var (GESet.singleton temp_pat))
            | Loc (l, None) -> update_loc l set |> ignore
            | _ -> ())
        | _ -> ())
      p_set
  | exception _ -> ()

let step_sc_for_file tbl =
  Hashtbl.iter
    (fun x set ->
      match x with
      | Var var -> SESet.iter (resolve_var var) set
      | Fld (Var var, (None, Some i)) ->
        let t = Unix.gettimeofday () in
        resolve_update (var, i) set;
        time_spent_in_update :=
          !time_spent_in_update +. (Unix.gettimeofday () -. t)
      | _ -> ())
    tbl

let step_sc added_file =
  if !linking then
    StringSet.iter
      (fun file ->
        try step_sc_for_file (Hashtbl.find sc file) with Not_found -> ())
      !files
  else try step_sc_for_file (Hashtbl.find sc added_file) with Not_found -> ()

let resolve_mem loc elt =
  match elt with
  | Top ->
    let t = Unix.gettimeofday () in
    update_abs_loc loc (GESet.singleton Top) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Const c when !first ->
    let t = Unix.gettimeofday () in
    update_abs_loc loc (GESet.singleton (Const c)) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Ctor (kappa, Static l) when !first || Worklist.mem (hash elt) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    let l' = List.map (fun i -> Loc (i, None)) l in
    update_abs_loc loc (GESet.singleton (Ctor_pat (kappa, l'))) |> ignore;
    time_spent_in_const := !time_spent_in_const +. (Unix.gettimeofday () -. t)
  | Var x when Worklist.mem (hash elt) prev_worklist ->
    let t = Unix.gettimeofday () in
    let set =
      SESet.filter
        (function
          | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
          | App_V (Prim p, l) ->
            if arg_len l < p.prim_arity then true else false
          | _ -> false)
        (try lookup_sc (Var x) with _ -> SESet.empty)
    in
    update_loc loc set |> ignore;
    if Hashtbl.mem grammar (Var x) then
      update_abs_loc loc (Hashtbl.find grammar (Var x)) |> ignore;
    time_spent_in_var := !time_spent_in_var +. (Unix.gettimeofday () -. t)
  | App_V (Prim p, l) when Worklist.mem (hash (Prim p)) prev_worklist ->
    let t = Unix.gettimeofday () in
    if p.prim_arity = arg_len l then
      update_loc loc (value_prim (p, l)) |> ignore;
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
        | Top -> update_abs_loc loc (GESet.singleton Top) |> ignore
        | Ctor_pat (_, l) ->
          let c_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter
                  (function
                    | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                    | App_V (Prim p, l) ->
                      if p.prim_arity <> arg_len l then true else false
                    | _ -> false)
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            else SESet.empty
          in
          let g_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (_, Some p) -> GESet.singleton p
              | Loc (l, None) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            else GESet.empty
          in
          update_loc loc c_set |> ignore;
          update_abs_loc loc g_set |> ignore
        | _ -> ())
      (try Hashtbl.find grammar (Var x) with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Fld (Var x, (Some k, Some i)) when Worklist.mem (hash (Var x)) prev_worklist
    ->
    let t = Unix.gettimeofday () in
    GESet.iter
      (function
        | Top -> update_abs_loc loc (GESet.singleton Top) |> ignore
        | Ctor_pat (Some k', l) when k = k' ->
          let c_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (l, _) ->
                SESet.filter
                  (function
                    | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                    | App_V (Prim p, l) ->
                      if p.prim_arity <> arg_len l then true else false
                    | _ -> false)
                  (try lookup_mem l with _ -> SESet.empty)
              | _ -> SESet.empty
            else SESet.empty
          in
          let g_set =
            if i < List.length l then
              match List.nth l i with
              | Loc (_, Some p) -> GESet.singleton p
              | Loc (l, None) -> (
                try Hashtbl.find abs_mem l with _ -> GESet.empty)
              | p -> GESet.singleton p
            else GESet.empty
          in
          update_loc loc c_set |> ignore;
          update_abs_loc loc g_set |> ignore
        | _ -> ())
      (try Hashtbl.find grammar (Var x) with _ -> GESet.empty);
    time_spent_in_fld := !time_spent_in_fld +. (Unix.gettimeofday () -. t)
  | Diff (Var x, p) when Worklist.mem (hash (Var x)) prev_worklist ->
    let t = Unix.gettimeofday () in
    update_abs_loc loc (filter_pat (Var x, p)) |> ignore;
    time_spent_in_filter := !time_spent_in_filter +. (Unix.gettimeofday () -. t)
  | _ -> ()

let step_mem_for_file tbl =
  Hashtbl.iter (fun loc set -> SESet.iter (resolve_mem loc) set) tbl

let step_mem added_file =
  if !linking then
    StringSet.iter
      (fun file ->
        try step_mem_for_file (Hashtbl.find memory file) with Not_found -> ())
      !files
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
