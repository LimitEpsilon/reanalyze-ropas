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

let rec print_se : se -> unit = function
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
    (match k with None -> prerr_string "-" | Some s -> prerr_string s);
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
  | Id (x, _) -> prerr_string (CL.Ident.unique_name x)

and print_ses (xs : se list) =
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

let show_sc_tbl (tbl : (se, SESet.t) Hashtbl.t) =
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
    tbl

let filter_closure = function
  | Fn (_, _) | App_v (_, None :: _) | Prim_v _ | Prim _ -> true
  | _ -> false

let show_closure_analysis tbl =
  prerr_endline "Closure analysis:";
  Hashtbl.iter
    (fun key data ->
      let set = SESet.filter filter_closure data in
      if SESet.is_empty set then ()
      else (
        print_se key;
        prerr_newline ();
        show_se_with_separator set "\t";
        prerr_newline ()))
    tbl

let print_sc_info () =
  show_var_se_tbl global_env;
  show_sc_tbl sc

let print_closure () =
  Format.flush_str_formatter () |> ignore;
  show_closure_analysis sc
