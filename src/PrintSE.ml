open SetExpression
open Reduce

let string_of_arithop : arithop -> string = function
  | INT x | INT32 x | INT64 x | FLOAT x | NATURALINT x -> (
    match x with
    | ADD -> "+"
    | SUB -> "-"
    | DIV -> "÷"
    | MUL -> "×"
    | NEG -> "~-"
    | ABS -> "abs"
    | MOD -> "mod"
    | AND -> "&&"
    | OR -> "||"
    | NOT -> "not"
    | XOR -> "xor"
    | LSL -> "lsl"
    | LSR -> "lsr"
    | ASR -> "asr"
    | SUCC -> "++"
    | PRED -> "--")

let string_of_relop : relop -> string = function
  | GEN x -> (
    match x with
    | EQ -> "=="
    | NE -> "!="
    | LT -> "<"
    | LE -> "<="
    | GT -> ">"
    | GE -> ">=")

let print_code_loc loc =
  CL.Location.print_loc Format.str_formatter loc;
  prerr_string (Format.flush_str_formatter ())

let print_loc = function
  | Expr_loc e -> print_code_loc e.exp_loc
  | Mod_loc m -> print_code_loc m.mod_loc
  | Bop_loc t -> print_code_loc t.val_loc

let print_param = function
  | None -> ()
  | Some x -> prerr_string (CL.Ident.name x)

let print_expr : type k. k expr -> unit = function
  | Expr_var p ->
    prerr_string "Expr_var (";
    prerr_string (CL.Ident.name p);
    prerr_string ")"
  | Expr loc ->
    prerr_string "Expr (";
    print_loc loc;
    prerr_string ")"

let print_tagged_expr : type k. k tagged_expr -> unit = function
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
    print_arr_with_separator arr ";";
    prerr_string ")"
  | Ctor (k, Dynamic i) ->
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
  | Arith (op, xs) ->
    Printf.eprintf "( %s ) " (string_of_arithop op);
    print_ses xs
  | Rel (rel, xs) ->
    Printf.eprintf "( %s ) " (string_of_relop rel);
    print_ses xs
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
    print_pattern_arr_with_separator arr ";";
    prerr_string ")"
  | Loc (i, p) ->
    prerr_string "(";
    prerr_int i;
    prerr_string ", ";
    (match p with Some p -> print_pattern p | _ -> ());
    prerr_string ")"
  | _ -> ()

and print_ses (xs : value se list) =
  prerr_string "[";
  List.iter print_se xs;
  prerr_string "]"

and print_se_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' != [] do
    match !l' with
    | hd :: tl ->
      prerr_string "(";
      print_se hd;
      prerr_string ")";
      if tl != [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

and print_pattern_arr_with_separator arr sep =
  let len = Array.length arr in
  let i = ref 0 in
  prerr_string "[";
  while !i < len do
    print_pattern arr.(!i);
    if !i < len - 1 then prerr_string sep;
    incr i
  done;
  prerr_string "]"

and print_expr_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' != [] do
    match !l' with
    | hd :: tl ->
      prerr_string "(";
      print_expr hd;
      prerr_string ")";
      if tl != [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

and print_option_list_with_separator l sep =
  let l' = ref l in
  prerr_string "[";
  while !l' != [] do
    match !l' with
    | Some hd :: tl ->
      prerr_string "(";
      print_se hd;
      prerr_string ")";
      if tl != [] then prerr_string sep;
      l' := tl
    | None :: tl ->
      if tl != [] then prerr_string sep;
      l' := tl
    | _ -> assert false
  done;
  prerr_string "]"

and print_arr_with_separator arr sep =
  let len = Array.length arr in
  let i = ref 0 in
  prerr_string "[";
  while !i < len do
    prerr_int arr.(!i);
    if !i < len - 1 then prerr_string sep;
    incr i
  done;
  prerr_string "]"

(* let show_env_map (env_map : globalenv) = *)
(*   Hashtbl.iter *)
(*     (fun param loc_tagged_expr -> *)
(*       prerr_string "Globalenv :\n param = "; *)
(*       print_param param; *)
(*       prerr_string "\n code_loc tagged_expr = "; *)
(*       print_tagged_expr loc_tagged_expr; *)
(*       prerr_newline ()) *)
(*     env_map *)

let show_var_se_tbl (var_to_se : var_se_tbl) =
  Hashtbl.iter
    (fun x se ->
      prerr_string "var_to_se :\n ident = ";
      prerr_string (CL.Ident.unique_name x);
      prerr_string "\n se = ";
      prerr_newline ();
      SESet.iter
        (fun x ->
          print_se x;
          prerr_newline ())
        se)
    var_to_se

let show_mem (mem : (int, SESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun key data ->
      prerr_string "mem :\n";
      prerr_int key;
      prerr_newline ();
      SESet.iter
        (fun x ->
          print_se x;
          prerr_newline ())
        data)
    mem

let show_sc_tbl (tbl : (value se, SESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun key data ->
      prerr_string "insensitive_sc :\n";
      print_se key;
      (match key with
      | Fld (_, _) -> prerr_string " <- "
      | _ -> prerr_string " = ");
      prerr_newline ();
      SESet.iter
        (fun x ->
          print_se x;
          prerr_newline ())
        data)
    tbl

let show_grammar (g : (pattern se, GESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun key data ->
      prerr_string "grammar :\n";
      print_pattern key;
      prerr_string " = ";
      prerr_newline ();
      GESet.iter
        (fun x ->
          print_pattern x;
          prerr_newline ())
        data)
    g

let show_abs_mem (a : (int, GESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun key data ->
      prerr_string "abs_mem :\n";
      prerr_int key;
      prerr_string " = ";
      prerr_newline ();
      GESet.iter
        (fun x ->
          print_pattern x;
          prerr_newline ())
        data)
    a

let print_sc_info () =
  show_mem mem;
  show_var_se_tbl var_to_se;
  show_sc_tbl sc

let print_result () =
  show_abs_mem abs_mem;
  show_grammar grammar

let count = ref 0
