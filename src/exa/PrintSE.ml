open SetExpression

module Loc = struct
  type t = loc

  let compare = compare
end

module LocSet = Set.Make (Loc)

let to_be_explained = ref LocSet.empty

let print_code_loc loc =
  CL.Location.print_loc Format.str_formatter loc;
  prerr_string (Format.flush_str_formatter ())

let print_loc (i, str) =
  match Hashtbl.find label_to_summary (i, str) with
  | Expr_loc e -> print_code_loc e.exp_loc
  | Mod_loc m -> print_code_loc m.mod_loc
  | Bop_loc t -> print_code_loc t.val_loc
  | Temp -> prerr_string ("temp_" ^ str ^ "_" ^ string_of_int i)

let print_param = function
  | None -> ()
  | Some (x, _) -> prerr_string (CL.Ident.name x)

let print_tagged_expr : tagged_expr -> unit = function
  | Val v ->
    prerr_string "Val (";
    print_loc v;
    prerr_string ")"
  | Packet p ->
    prerr_string "Packet (";
    print_loc p;
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
  | Prim_v ({prim_name}, list) ->
    prerr_string "PrimV (";
    prerr_string prim_name;
    prerr_string ", ";
    print_option_list_with_separator list ";";
    prerr_string ")"
  | Prim_p ({prim_name}, list) ->
    prerr_string "PrimP (";
    prerr_string prim_name;
    prerr_string ", ";
    print_option_list_with_separator list ";";
    prerr_string ")"
  | App_v (e, list) ->
    prerr_string "AppV (";
    print_tagged_expr e;
    prerr_string ", ";
    print_option_list_with_separator list ";";
    prerr_string ")"
  | App_p (e, list) ->
    prerr_string "AppP (";
    print_tagged_expr e;
    prerr_string ", ";
    print_option_list_with_separator list ";";
    prerr_string ")"
  | Ctor (k, arr) ->
    prerr_string "Ctor (";
    (match k with None -> prerr_string " " | Some s -> prerr_string s);
    prerr_string ", ";
    print_list_with_separator arr ";";
    prerr_string ")"
  | Arr (i, _) ->
    prerr_string "Arr (";
    prerr_string "malloc ";
    prerr_string (string_of_int i);
    prerr_string ")"
  | Fld (e, lbl) ->
    prerr_string "Fld (";
    print_tagged_expr e;
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
  | Loc (i, _) -> prerr_string ("!ℓ_" ^ string_of_int i)
  | Diff (x, y) ->
    prerr_string "(";
    print_tagged_expr x;
    prerr_string ")-(";
    print_pattern y;
    prerr_string ")"
  | Id (x, _) -> prerr_string (CL.Ident.unique_name x)
  | _ -> ()

and print_pattern : pattern se -> unit = function
  | Top -> prerr_string "⊤"
  | Const c -> prerr_string (CL.Printpat.pretty_const c)
  | Ctor_pat (k, arr) ->
    prerr_string "Ctor (";
    (match k with None -> prerr_string " " | Some s -> prerr_string s);
    prerr_string ", ";
    print_pattern_list_with_separator arr ";";
    prerr_string ")"
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
      print_loc hd;
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
      print_tagged_expr hd;
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
      prerr_string "ℓ_";
      prerr_int (fst hd);
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

let show_var_se_tbl (var_to_se : var_se_tbl) =
  Hashtbl.iter
    (fun _ tbl ->
      Hashtbl.iter
        (fun x e ->
          prerr_string "var_to_se :\n ident = ";
          prerr_string (CL.Ident.unique_name x);
          prerr_string "\n se = ";
          print_tagged_expr e;
          prerr_newline ())
        tbl)
    var_to_se

let show_local_env (env : SEnv.t) =
  let first = ref true in
  prerr_string "{";
  SEnv.Internal.iter
    (fun (x, _) expr ->
      if !first then first := false else prerr_string "; ";
      prerr_string (CL.Ident.unique_name x);
      prerr_string "↦ ";
      print_tagged_expr expr;
      prerr_newline ())
    env;
  prerr_string "}"

let show_sc_tbl (tbl : (value se, SESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun lhs data ->
      if SESet.is_empty data then ()
      else (
        print_se lhs;
        (match lhs with
        | Fld (_, _) -> prerr_string " <- "
        | _ -> prerr_string " = ");
        prerr_newline ();
        show_se_with_separator data "\t";
        prerr_newline ()))
    tbl

let tracked_vars : (value se, unit) Hashtbl.t = Hashtbl.create 10
let track_path = ref false

(* let rec track_exception (x : value se) (exn : pattern se) = *)
(*   let propagate = function *)
(*     | Var x -> ( *)
(*       let exns = try Hashtbl.find grammar x with _ -> GESet.empty in *)
(*       let filter p = *)
(*         exn = p *)
(*         || *)
(*         match exn with *)
(*         | Ctor_pat (k, _) -> ( *)
(*           match p with Ctor_pat (k', _) -> k = k' | _ -> false) *)
(*         | _ -> false *)
(*       in *)
(*       let filtered = GESet.filter filter exns in *)
(*       if not (GESet.is_empty filtered) then *)
(*         let () = *)
(*           if !track_path then ( *)
(*             print_tagged_expr x; *)
(*             prerr_newline ()) *)
(*         in *)
(*         match x with *)
(*         | Val (Expr e) -> *)
(*           prerr_string "  raised from: "; *)
(*           print_loc e; *)
(*           prerr_newline () *)
(*         | _ -> *)
(*           SESet.iter *)
(*             (function *)
(*               | Var x -> track_exception (Var x) exn *)
(*               | Diff (Var x, _) -> track_exception (Var x) exn *)
(*               | _ -> ()) *)
(*             (lookup_sc (Var x))) *)
(*     | _ -> assert false *)
(*   in *)
(*   match Hashtbl.find tracked_vars x with *)
(*   | exception Not_found -> *)
(*     Hashtbl.add tracked_vars x (); *)
(*     propagate x *)
(*   | () -> () *)

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
              | Var (Packet loc) ->
                Cstr.iter
                  (fun _ tbl ->
                    let exns = lookup_sc tbl (Var (Packet loc)) in
                    if SESet.is_empty exns then ()
                    else (
                      prerr_string " Escaped from ";
                      print_loc loc;
                      prerr_endline ":";
                      SESet.iter
                        (function
                          | Ctor (Some ctor, l) ->
                            printed := true;
                            prerr_string "\t";
                            track_path := ctor = !Common.Cli.ctor_to_track;
                            prerr_string (" " ^ ctor ^ " with arguments ");
                            print_list_with_separator l ";";
                            prerr_newline ();
                            Hashtbl.clear tracked_vars
                            (* track_exception (Var (Packet (Expr loc))) exn; *)
                            (* explain_abs_mem () *)
                          | Top ->
                            printed := true;
                            prerr_string "\t";
                            print_pattern Top;
                            prerr_newline ();
                            Hashtbl.clear tracked_vars
                          (* track_exception (Var (Packet (Expr loc))) exn *)
                          | _ -> ())
                        exns))
                  !sc
              | _ -> ())
            data
        in
        if !printed then () else prerr_string " No escaping exceptions\n\n")
    tbl

let show_closure_analysis tbl =
  prerr_endline "Closure analysis:";
  Hashtbl.iter
    (fun lhs data ->
      let set =
        SESet.filter
          (fun x ->
            match x with
            | App_v (_, _) | Fn (_, _) | Prim _ -> true
            | _ -> false)
          data
      in
      if SESet.is_empty set then ()
      else (
        print_se lhs;
        prerr_newline ();
        show_se_with_separator set "\t";
        prerr_newline ()))
    tbl

let print_sc_info () =
  show_var_se_tbl global_env;
  Cstr.iter
    (fun env tbl ->
      prerr_string "Under ";
      show_local_env env;
      prerr_newline ();
      show_sc_tbl tbl)
    !sc

let print_exa () =
  Format.flush_str_formatter () |> ignore;
  show_exn_of_file exn_of_file

let print_closure () =
  Format.flush_str_formatter () |> ignore;
  Cstr.iter
    (fun env tbl ->
      prerr_string "Under ";
      show_local_env env;
      prerr_newline ();
      show_closure_analysis tbl)
    !sc
