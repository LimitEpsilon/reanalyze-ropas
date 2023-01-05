open SetExpression

let to_be_explained = ref LocSet.empty

let print_code_loc loc =
  CL.Location.print_loc Format.str_formatter loc;
  prerr_string (Format.flush_str_formatter ())

let print_loc loc =
  match Hashtbl.find label_to_summary loc with
  | Expr_loc e -> print_code_loc e.exp_loc
  | Mod_loc m -> print_code_loc m.mod_loc
  | Bop_loc t -> print_code_loc t.val_loc

let print_param = function
  | None -> ()
  | Some (x, _) -> prerr_string (CL.Ident.name x)

let print_expr : type k. k expr -> unit = function
  | Expr_var (p, _) ->
    prerr_string "Expr_var (";
    prerr_string (CL.Ident.name p);
    prerr_string ")"
  | Expr loc ->
    prerr_string "Expr (";
    print_loc loc;
    prerr_string ")"

let print_tagged_expr : tagged_expr -> unit = function
  | Val v ->
    prerr_string "Val (";
    print_expr v;
    prerr_string ")"
  | Packet p ->
    prerr_string "Packet (";
    print_expr p;
    prerr_string ")"

let rec print_se : value se -> unit = function
  | Top -> prerr_string "⊤"
  | Const c -> prerr_string (CL.Printpat.pretty_const c)
  | Fn (p, list) ->
    prerr_string "λ";
    print_param p;
    prerr_string ".";
    print_expr_list_with_separator list ";"
  | Prim {prim_name} -> prerr_string ("Prim (" ^ prim_name ^ ")")
  | Var e ->
    prerr_string "X (";
    print_tagged_expr e;
    prerr_string ")"
  | App_V (se, list) ->
    prerr_string "AppV (";
    print_se se;
    prerr_string ", ";
    print_option_list_with_separator list ";";
    prerr_string ")"
  | App_P (se, list) ->
    prerr_string "AppP (";
    print_se se;
    prerr_string ", ";
    print_option_list_with_separator list ";";
    prerr_string ")"
  | Ctor (k, Static arr) ->
    prerr_string "Ctor (";
    (match k with None -> prerr_string " " | Some s -> prerr_string s);
    prerr_string ", ";
    print_list_with_separator arr ";";
    prerr_string ")"
  | Ctor (k, Dynamic (i, _)) ->
    prerr_string "Ctor (";
    (match k with None -> prerr_string " " | Some s -> prerr_string s);
    prerr_string "malloc ";
    prerr_string (string_of_int i);
    prerr_string ")"
  | Fld (se, lbl) ->
    prerr_string "Fld (";
    print_se se;
    prerr_string ", (";
    (match lbl with
    | None, Some i ->
      prerr_string " , ";
      prerr_int i
    | Some s, Some i ->
      prerr_string s;
      prerr_string ", ";
      prerr_int i
    | _, None -> prerr_string " , ");
    prerr_string "))"
  | Diff (x, y) ->
    prerr_string "(";
    print_se x;
    prerr_string ")-(";
    print_pattern y;
    prerr_string ")"
  | _ -> ()

and print_pattern : pattern se -> unit = function
  | Top -> prerr_string "⊤"
  | Const c -> prerr_string (CL.Printpat.pretty_const c)
  | Var e ->
    prerr_string "X (";
    print_tagged_expr e;
    prerr_string ")"
  | Ctor_pat (k, arr) ->
    prerr_string "Ctor (";
    (match k with None -> prerr_string " " | Some s -> prerr_string s);
    prerr_string ", ";
    print_pattern_list_with_separator arr ";";
    prerr_string ")"
  | Arr_pat (i, _) ->
    prerr_string "Arr (";
    prerr_string "ℓ_";
    print_int i;
    prerr_string ")"
  | Loc ((i, name), _) ->
    prerr_string "ℓ_";
    prerr_int i;
    to_be_explained := LocSet.add (i, name) !to_be_explained
  | _ -> ()

and print_ses (xs : value se list) =
  prerr_string "[";
  List.iter print_se xs;
  prerr_string "]"

and print_se_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' <> [] do
    match !l' with
    | hd :: tl ->
      prerr_string "(";
      print_se hd;
      prerr_string ")";
      if tl <> [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

and print_pattern_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' <> [] do
    match !l' with
    | hd :: tl ->
      print_pattern hd;
      if tl <> [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

and print_expr_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' <> [] do
    match !l' with
    | hd :: tl ->
      prerr_string "(";
      print_expr hd;
      prerr_string ")";
      if tl <> [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

and print_option_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' <> [] do
    match !l' with
    | Some hd :: tl ->
      prerr_string "(";
      print_se hd;
      prerr_string ")";
      if tl <> [] then prerr_string sep;
      l' := tl
    | None :: tl ->
      if tl <> [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

and print_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' <> [] do
    match !l' with
    | hd :: tl ->
      prerr_int (fst (fst hd));
      if tl <> [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

let show_se_with_separator set sep =
  SESet.iter
    (fun x ->
      prerr_string sep;
      print_se x;
      prerr_newline ())
    set

let show_pattern_with_separator set sep =
  GESet.iter
    (fun x ->
      prerr_string sep;
      print_pattern x;
      prerr_newline ())
    set

let show_var_se_tbl (var_to_se : var_se_tbl) =
  Hashtbl.iter
    (fun _ tbl ->
      Hashtbl.iter
        (fun x se ->
          prerr_string "var_to_se :\n ident = ";
          prerr_string (CL.Ident.unique_name x);
          prerr_string "\n se = ";
          prerr_newline ();
          show_se_with_separator se "\t";
          prerr_newline ())
        tbl)
    var_to_se

let show_mem (mem : (string, (loc, SESet.t) Hashtbl.t) Hashtbl.t) =
  Hashtbl.iter
    (fun _ mem ->
      Hashtbl.iter
        (fun (key, _) data ->
          if SESet.is_empty data then ()
          else (
            prerr_string "mem :\n";
            prerr_int key;
            prerr_newline ();
            show_se_with_separator data "\t";
            prerr_newline ()))
        mem)
    mem

let show_sc_tbl (tbl : (string, (value se, SESet.t) Hashtbl.t) Hashtbl.t) =
  Hashtbl.iter
    (fun _ tbl ->
      Hashtbl.iter
        (fun key data ->
          if SESet.is_empty data then ()
          else (
            prerr_string "sc :\n";
            print_se key;
            (match key with
            | Fld (_, _) -> prerr_string " <- "
            | _ -> prerr_string " = ");
            prerr_newline ();
            show_se_with_separator data "\t";
            prerr_newline ()))
        tbl)
    tbl

let show_grammar (g : (tagged_expr, GESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun key data ->
      if GESet.is_empty data then ()
      else (
        prerr_string "grammar :\n";
        print_tagged_expr key;
        prerr_string " = ";
        prerr_newline ();
        show_pattern_with_separator data "\t";
        prerr_newline ()))
    g

let show_abs_mem (a : (loc, GESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun (key, _) data ->
      if GESet.is_empty data then ()
      else (
        prerr_string "abs_mem :\n";
        prerr_int key;
        prerr_string " = ";
        prerr_newline ();
        show_pattern_with_separator data "\t";
        prerr_newline ()))
    a

let tracked_vars = Hashtbl.create 10
let track_path = ref false

let rec track_exception (x : value se) (exn : pattern se) =
  let propagate = function
    | Var x -> (
      let exns = try Hashtbl.find grammar x with _ -> GESet.empty in
      let filter p =
        exn = p
        ||
        match exn with
        | Ctor_pat (k, _) -> (
          match p with Ctor_pat (k', _) -> k = k' | _ -> false)
        | _ -> false
      in
      let filtered = GESet.filter filter exns in
      if not (GESet.is_empty filtered) then
        let () =
          if !track_path then (
            print_tagged_expr x;
            prerr_newline ())
        in
        match x with
        | Val (Expr e) ->
          prerr_string "  raised from: ";
          print_loc e;
          prerr_newline ()
        | _ ->
          SESet.iter
            (function
              | Var x -> track_exception (Var x) exn
              | Diff (Var x, _) -> track_exception (Var x) exn
              | _ -> ())
            (lookup_sc (Var x)))
    | _ -> assert false
  in
  match Hashtbl.find tracked_vars x with
  | exception Not_found ->
    Hashtbl.add tracked_vars x ();
    propagate x
  | () -> ()

let explain_abs_mem () =
  if not (LocSet.is_empty !to_be_explained) then
    prerr_endline " Where abstract locations contain:";
  LocSet.iter
    (fun (i, name) ->
      let set = try Hashtbl.find abs_mem (i, name) with _ -> GESet.empty in
      prerr_string " ℓ_";
      prerr_int i;
      prerr_string ":\n";
      show_pattern_with_separator set "  ")
    !to_be_explained;
  to_be_explained := LocSet.empty

let show_exn_of_file (tbl : (string, value se list) Hashtbl.t) =
  Hashtbl.iter
    (fun key data ->
      prerr_string "Exceptions in file ";
      prerr_string key;
      prerr_newline ();
      if data = [] then prerr_string " No escaping exceptions\n\n"
      else
        let printed = ref false in
        let () =
          List.iter
            (function
              | Var (Packet (Expr loc)) ->
                let set =
                  try Hashtbl.find grammar (Packet (Expr loc))
                  with _ -> GESet.empty
                in
                if GESet.is_empty set then ()
                else (
                  printed := true;
                  prerr_string " Escaped from ";
                  print_loc loc;
                  prerr_endline ":";
                  GESet.iter
                    (function
                      | Ctor_pat (Some ctor, l) as exn ->
                        track_path := ctor = !Common.Cli.ctor_to_track;
                        prerr_string (" " ^ ctor ^ " with arguments ");
                        print_pattern_list_with_separator l ";";
                        prerr_string ":\n";
                        Hashtbl.clear tracked_vars;
                        track_exception (Var (Packet (Expr loc))) exn;
                        explain_abs_mem ()
                      | exn ->
                        prerr_string " ";
                        print_pattern exn;
                        prerr_string ":\n";
                        Hashtbl.clear tracked_vars;
                        track_exception (Var (Packet (Expr loc))) exn)
                    set;
                  prerr_newline ())
              | _ -> ())
            data
        in
        if !printed then () else prerr_string " No escaping exceptions\n\n")
    tbl

let show_closure_analysis tbl =
  prerr_endline "Closure analysis:";
  Hashtbl.iter
    (fun _ tbl ->
      Hashtbl.iter
        (fun key data ->
          let set =
            SESet.filter
              (fun x ->
                match x with
                | App_V (_, _) | Fn (_, _) | Prim _ -> true
                | _ -> false)
              data
          in
          if SESet.is_empty set then ()
          else (
            print_se key;
            prerr_newline ();
            show_se_with_separator set "\t";
            prerr_newline ()))
        tbl)
    tbl

let print_sc_info () =
  show_mem memory;
  show_var_se_tbl var_to_se;
  show_sc_tbl sc

let print_grammar () =
  show_abs_mem abs_mem;
  show_grammar grammar

let print_exa () =
  Format.flush_str_formatter () |> ignore;
  show_exn_of_file exn_of_file

let print_closure () =
  Format.flush_str_formatter () |> ignore;
  show_closure_analysis sc
