open SetExpression
open PrintSE

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
  | x, p when x = p -> GESet.empty
  | x, Const c when x <> Const c -> GESet.singleton x
  | (Ctor_pat (kappa, _) as x), Ctor_pat (kappa', _) when kappa <> kappa' ->
    GESet.singleton x
  | Top, Ctor_pat (kappa, arr) ->
    filter_pat
      (Ctor_pat (kappa, Array.map (fun _ -> Top) arr), Ctor_pat (kappa, arr))
  | Var x, p when Hashtbl.mem grammar (Var x) ->
    GESet.fold
      (fun y acc -> GESet.union (filter_pat (y, p)) acc)
      (Hashtbl.find grammar (Var x))
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
  | Ctor_pat (kappa, arr), Ctor_pat (kappa', arr')
    when kappa = kappa' && Array.length arr = Array.length arr' ->
    let acc = ref GESet.empty in
    let i = ref 0 in
    let arr = Array.copy arr in
    let len = Array.length arr in
    while !i < len do
      let ith = filter_pat (arr.(!i), arr'.(!i)) in
      let set =
        GESet.map
          (fun x ->
            let temp = Array.copy arr in
            temp.(!i) <- x;
            Ctor_pat (kappa, temp))
          ith
      in
      acc := GESet.union !acc set;
      (if arr'.(!i) <> Top then
       let update_with =
         match arr.(!i) with
         | Loc (l, _) -> Loc (l, Some arr'.(!i))
         | _ -> arr'.(!i)
       in
       arr.(!i) <- update_with);
      incr i
    done;
    !acc
  | _ -> GESet.empty

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
  | x, p when x = p ->
    prerr_endline "lhs = rhs";
    GESet.empty
  | x, Const c when x <> Const c ->
    prerr_endline "rhs = const";
    GESet.singleton x
  | (Ctor_pat (kappa, _) as x), Ctor_pat (kappa', _) when kappa <> kappa' ->
    prerr_endline "lhs, rhs = ctor, no filter";
    GESet.singleton x
  | Top, Ctor_pat (kappa, arr) ->
    prerr_endline "lhs = Top, coerce into ctor";
    filter_pat_debug
      (Ctor_pat (kappa, Array.map (fun _ -> Top) arr), Ctor_pat (kappa, arr))
  | Var x, p when Hashtbl.mem grammar (Var x) ->
    prerr_endline "lhs = var";
    GESet.fold
      (fun y acc -> GESet.union (filter_pat_debug (y, p)) acc)
      (Hashtbl.find grammar (Var x))
      GESet.empty
  | Loc (l, None), p ->
    prerr_endline "lhs = loc without pat";
    GESet.map
      (fun x -> Loc (l, Some x))
      (GESet.fold
         (fun y acc -> GESet.union (filter_pat_debug (y, p)) acc)
         (try Hashtbl.find abs_mem l with _ -> GESet.empty)
         GESet.empty)
  | Loc (l, Some p), p' ->
    prerr_endline "lhs = loc with pat";
    GESet.map (fun x -> Loc (l, Some x)) (filter_pat_debug (p, p'))
  | Ctor_pat (kappa, arr), Ctor_pat (kappa', arr')
    when kappa = kappa' && Array.length arr = Array.length arr' ->
    prerr_endline "lhs, rhs = ctor, filter";
    let acc = ref GESet.empty in
    let i = ref 0 in
    let arr = Array.copy arr in
    let len = Array.length arr in
    while !i < len do
      let ith = filter_pat_debug (arr.(!i), arr'.(!i)) in
      let set =
        GESet.map
          (fun x ->
            let temp = Array.copy arr in
            temp.(!i) <- x;
            Ctor_pat (kappa, temp))
          ith
      in
      acc := GESet.union !acc set;
      (if arr'.(!i) <> Top then
       let update_with =
         match arr.(!i) with
         | Loc (l, _) -> Loc (l, Some arr'.(!i))
         | _ -> arr'.(!i)
       in
       arr.(!i) <- update_with);
      incr i
    done;
    !acc
  | _ ->
    prerr_endline "else";
    GESet.empty

let allocated = ref SESet.empty

let value_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_V (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_V (x, [Some y]))
  | {CL.Primitive.prim_name = "%identity"}, [Some x] -> SESet.singleton x
  | {CL.Primitive.prim_name = "%ignore"}, [Some _] ->
    SESet.singleton (Ctor (Some "()", Static [||]))
  | {CL.Primitive.prim_name = "%field0"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 0)))
  | {CL.Primitive.prim_name = "%field1"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 1)))
  | {CL.Primitive.prim_name = "%setfield0"}, [Some x; Some y] ->
    update_c (Fld (x, (None, Some 0))) (SESet.singleton y);
    SESet.singleton (Ctor (Some "()", Static [||]))
  | {CL.Primitive.prim_name = "%makemutable"}, [Some x] ->
    if SESet.mem x !allocated then SESet.empty
    else (
      allocated := SESet.add x !allocated;
      let i = new_memory () in
      update_loc i (SESet.singleton x);
      SESet.singleton (Ctor (None, Static [|i|])))
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

let resolve_var var set =
  let resolve = function
    | Top -> update_g (Var var) (GESet.singleton Top)
    | Const c -> update_g (Var var) (GESet.singleton (Const c))
    | Ctor (kappa, Static arr) ->
      let arr' = Array.map (fun i -> Loc (i, None)) arr in
      update_g (Var var) (GESet.singleton (Ctor_pat (kappa, arr')))
    | Var x ->
      let set =
        SESet.filter
          (function
            | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
            | App_V (Prim p, l) ->
              if arg_len l < p.prim_arity then true else false
            | _ -> false)
          (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
      in
      update_c (Var var) set;
      if Hashtbl.mem grammar (Var x) then
        update_g (Var var) (Hashtbl.find grammar (Var x))
    | App_V (Prim p, l) ->
      if p.prim_arity = arg_len l then update_c (Var var) (value_prim (p, l))
    | App_P (Prim p, l) ->
      if p.prim_arity = arg_len l then update_c (Var var) (packet_prim (p, l))
    | App_V (Var x, []) ->
      SESet.iter
        (function
          | Fn (None, l) ->
            let set = SESet.of_list (List.map (fun x -> Var (Val x)) l) in
            update_c (Var var) set
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | App_P (Var x, []) ->
      SESet.iter
        (function
          | Fn (None, l) ->
            let set = SESet.of_list (List.map (fun x -> Var (Packet x)) l) in
            update_c (Var var) set
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | App_V (Var x, Some (Var y) :: tl) ->
      SESet.iter
        (function
          | Prim p ->
            update_c (Var var)
              (SESet.singleton (App_V (Prim p, Some (Var y) :: tl)))
          | Fn (Some x, l) ->
            let values =
              if tl <> [] then
                SESet.of_list (List.map (fun e -> App_V (Var (Val e), tl)) l)
              else SESet.of_list (List.map (fun e -> Var (Val e)) l)
            in
            update_c (Var var) values;
            update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y))
          | App_V (Prim p, l) when arg_len l < p.prim_arity ->
            let app =
              SESet.singleton
                (App_V (Prim p, merge_args (l, Some (Var y) :: tl)))
            in
            update_c (Var var) app
          | App_V (f, None :: tl') ->
            let app =
              SESet.singleton (App_V (f, Some (Var y) :: merge_args (tl', tl)))
            in
            update_c (Var var) app
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | App_P (Var x, Some (Var y) :: tl) ->
      SESet.iter
        (function
          | Prim p ->
            update_c (Var var)
              (SESet.singleton (App_P (Prim p, Some (Var y) :: tl)))
          | Fn (Some x, l) ->
            let app_p =
              if tl <> [] then
                SESet.of_list (List.map (fun e -> App_P (Var (Val e), tl)) l)
              else SESet.empty
            in
            let body_p = SESet.of_list (List.map (fun e -> Var (Packet e)) l) in
            update_c (Var var) (SESet.union app_p body_p);
            update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y))
          | App_V (Prim p, l) when arg_len l < p.prim_arity ->
            let app =
              SESet.singleton
                (App_P (Prim p, merge_args (l, Some (Var y) :: tl)))
            in
            update_c (Var var) app
          | App_V (f, None :: tl') ->
            let app =
              SESet.singleton (App_P (f, Some (Var y) :: merge_args (tl', tl)))
            in
            update_c (Var var) app
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | Fld (Var x, (None, Some i)) ->
      GESet.iter
        (function
          | Top -> update_g (Var var) (GESet.singleton Top)
          | Ctor_pat (_, arr) ->
            let c_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (l, _) ->
                  SESet.filter
                    (function
                      | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                      | App_V (Prim p, l) ->
                        if p.prim_arity <> arg_len l then true else false
                      | _ -> false)
                    (try Hashtbl.find mem l with _ -> SESet.empty)
                | _ -> SESet.empty
              else SESet.empty
            in
            let g_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (_, Some p) -> GESet.singleton p
                | Loc (l, None) ->
                  if Hashtbl.mem abs_mem l then Hashtbl.find abs_mem l
                  else GESet.empty
                | p -> GESet.singleton p
              else GESet.empty
            in
            update_c (Var var) c_set;
            update_g (Var var) g_set
          | _ -> ())
        (try Hashtbl.find grammar (Var x) with _ -> GESet.empty)
    | Fld (Var x, (Some k, Some i)) ->
      GESet.iter
        (function
          | Top -> update_g (Var var) (GESet.singleton Top)
          | Ctor_pat (Some k', arr) when k = k' ->
            let c_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (l, _) ->
                  SESet.filter
                    (function
                      | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                      | App_V (Prim p, l) ->
                        if p.prim_arity <> arg_len l then true else false
                      | _ -> false)
                    (try Hashtbl.find mem l with _ -> SESet.empty)
                | _ -> SESet.empty
              else SESet.empty
            in
            let g_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (_, Some p) -> GESet.singleton p
                | Loc (l, None) ->
                  if Hashtbl.mem abs_mem l then Hashtbl.find abs_mem l
                  else GESet.empty
                | p -> GESet.singleton p
              else GESet.empty
            in
            update_c (Var var) c_set;
            update_g (Var var) g_set
          | _ -> ())
        (try Hashtbl.find grammar (Var x) with _ -> GESet.empty)
    | Diff (Var x, p) ->
      if !Common.Cli.debug_pat then (
        (match x with
        | Val (Expr_var x) -> prerr_endline (CL.Ident.name x)
        | _ -> ());
        update_g (Var var) (filter_pat_debug (Var x, p)))
      else update_g (Var var) (filter_pat (Var x, p))
    | _ -> ()
  in
  SESet.iter resolve set

let resolve_update (var, i) set =
  match Hashtbl.find grammar (Var var) with
  | p_set ->
    GESet.iter
      (function
        | Ctor_pat (_, arr) -> (
          if i < Array.length arr then
            match arr.(i) with Loc (l, _) -> update_loc l set | _ -> ())
        | _ -> ())
      p_set
  | exception _ -> ()

let step_sc () =
  Hashtbl.iter
    (fun x set ->
      match x with
      | Var var -> resolve_var var set
      | Fld (Var var, (None, Some i)) -> resolve_update (var, i) set
      | _ -> ())
    sc

let resolve_mem loc set =
  let resolve = function
    | Top -> update_abs_loc loc (GESet.singleton Top)
    | Const c -> update_abs_loc loc (GESet.singleton (Const c))
    | Ctor (kappa, Static arr) ->
      let arr' = Array.map (fun i -> Loc (i, None)) arr in
      update_abs_loc loc (GESet.singleton (Ctor_pat (kappa, arr')))
    | Var x ->
      let set =
        SESet.filter
          (function
            | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
            | App_V (Prim p, l) ->
              if arg_len l < p.prim_arity then true else false
            | _ -> false)
          (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
      in
      update_loc loc set;
      if Hashtbl.mem grammar (Var x) then
        update_abs_loc loc (Hashtbl.find grammar (Var x))
    | App_V (Prim p, l) ->
      if p.prim_arity = arg_len l then update_loc loc (value_prim (p, l))
    | App_P (Prim p, l) ->
      if p.prim_arity = arg_len l then update_loc loc (packet_prim (p, l))
    | App_V (Var x, []) ->
      SESet.iter
        (function
          | Fn (None, l) ->
            let set = SESet.of_list (List.map (fun x -> Var (Val x)) l) in
            update_loc loc set
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | App_P (Var x, []) ->
      SESet.iter
        (function
          | Fn (None, l) ->
            let set = SESet.of_list (List.map (fun x -> Var (Packet x)) l) in
            update_loc loc set
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | App_V (Var x, Some (Var y) :: tl) ->
      SESet.iter
        (function
          | Prim p ->
            update_loc loc
              (SESet.singleton (App_V (Prim p, Some (Var y) :: tl)))
          | Fn (Some x, l) ->
            let values =
              if tl <> [] then
                SESet.of_list (List.map (fun e -> App_V (Var (Val e), tl)) l)
              else SESet.of_list (List.map (fun e -> Var (Val e)) l)
            in
            update_loc loc values;
            update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y))
          | App_V (Prim p, l) when arg_len l < p.prim_arity ->
            let app =
              SESet.singleton
                (App_V (Prim p, merge_args (l, Some (Var y) :: tl)))
            in
            update_loc loc app
          | App_V (f, None :: tl') ->
            let app =
              SESet.singleton (App_V (f, Some (Var y) :: merge_args (tl', tl)))
            in
            update_loc loc app
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | App_P (Var x, Some (Var y) :: tl) ->
      SESet.iter
        (function
          | Prim p ->
            update_loc loc
              (SESet.singleton (App_P (Prim p, Some (Var y) :: tl)))
          | Fn (Some x, l) ->
            let app_p =
              if tl <> [] then
                SESet.of_list (List.map (fun e -> App_P (Var (Val e), tl)) l)
              else SESet.empty
            in
            let body_p = SESet.of_list (List.map (fun e -> Var (Packet e)) l) in
            update_loc loc (SESet.union app_p body_p);
            update_c (Var (Val (Expr_var x))) (SESet.singleton (Var y))
          | App_V (Prim p, l) ->
            let app =
              SESet.singleton
                (App_P (Prim p, merge_args (l, Some (Var y) :: tl)))
            in
            update_loc loc app
          | App_V (f, None :: tl') ->
            let app =
              SESet.singleton (App_P (f, Some (Var y) :: merge_args (tl', tl)))
            in
            update_loc loc app
          | _ -> ())
        (try Hashtbl.find sc (Var x) with _ -> SESet.empty)
    | Fld (Var x, (None, Some i)) ->
      GESet.iter
        (function
          | Top -> update_abs_loc loc (GESet.singleton Top)
          | Ctor_pat (_, arr) ->
            let c_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (l, _) ->
                  SESet.filter
                    (function
                      | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                      | App_V (Prim p, l) ->
                        if p.prim_arity <> arg_len l then true else false
                      | _ -> false)
                    (try Hashtbl.find mem l with _ -> SESet.empty)
                | _ -> SESet.empty
              else SESet.empty
            in
            let g_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (_, Some p) -> GESet.singleton p
                | Loc (l, None) ->
                  if Hashtbl.mem abs_mem l then Hashtbl.find abs_mem l
                  else GESet.empty
                | p -> GESet.singleton p
              else GESet.empty
            in
            update_loc loc c_set;
            update_abs_loc loc g_set
          | _ -> ())
        (try Hashtbl.find grammar (Var x) with _ -> GESet.empty)
    | Fld (Var x, (Some k, Some i)) ->
      GESet.iter
        (function
          | Top -> update_abs_loc loc (GESet.singleton Top)
          | Ctor_pat (Some k', arr) when k = k' ->
            let c_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (l, _) ->
                  SESet.filter
                    (function
                      | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
                      | App_V (Prim p, l) ->
                        if p.prim_arity <> arg_len l then true else false
                      | _ -> false)
                    (try Hashtbl.find mem l with _ -> SESet.empty)
                | _ -> SESet.empty
              else SESet.empty
            in
            let g_set =
              if i < Array.length arr then
                match arr.(i) with
                | Loc (_, Some p) -> GESet.singleton p
                | Loc (l, None) ->
                  if Hashtbl.mem abs_mem l then Hashtbl.find abs_mem l
                  else GESet.empty
                | p -> GESet.singleton p
              else GESet.empty
            in
            update_loc loc c_set;
            update_abs_loc loc g_set
          | _ -> ())
        (try Hashtbl.find grammar (Var x) with _ -> GESet.empty)
    | Diff (Var x, p) -> update_abs_loc loc (filter_pat (Var x, p))
    | _ -> ()
  in
  SESet.iter resolve set

let step_mem () = Hashtbl.iter resolve_mem mem

let solve () =
  changed := false;
  step_sc ();
  step_mem ();
  while !changed do
    changed := false;
    step_sc ();
    step_mem ()
  done
