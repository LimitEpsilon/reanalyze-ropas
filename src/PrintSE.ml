open SetExpression

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

let print_loc loc =
  CL.Location.print_loc Format.str_formatter loc;
  prerr_string (Format.flush_str_formatter ())

let print_param par =
  prerr_string "[";
  List.iter print_loc par;
  prerr_string "]"

let print_expr : type k. k expr -> unit = function
  | Expr_var p ->
    prerr_string "Expr_var (";
    print_param p;
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

let rec print_se : unit se -> unit = function
  | Top -> prerr_string "⊤"
  | Const c -> prerr_string (CL.Printpat.pretty_const c)
  | Fn (p, list) ->
    prerr_string "<";
    print_param p;
    print_expr_list_with_separator list ";";
    prerr_string ">"
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
  | Ctor (k, Some arr, plus_alpha) ->
    prerr_string "Con (";
    (match k with None -> prerr_string " " | Some (s, _) -> prerr_string s);
    print_arr_with_separator arr ";";
    (match plus_alpha with
    | None -> ()
    | Some plus_alpha -> prerr_string ("+α_" ^ string_of_int plus_alpha));
    prerr_string ")"
  | Ctor (k, None, plus_alpha) ->
    prerr_string "Con (";
    (match k with None -> prerr_string " " | Some (s, _) -> prerr_string s);
    (match plus_alpha with
    | None -> ()
    | Some plus_alpha -> prerr_string ("α_" ^ string_of_int plus_alpha));
    prerr_string ")"
  | Fld (se, lbl) ->
    prerr_string "Fld (";
    print_se se;
    prerr_string ", (";
    (match lbl with
    | None, x ->
      prerr_string " , ";
      print_se x
    | Some (s, _), x ->
      prerr_string s;
      prerr_string ", ";
      print_se x);
    prerr_string "))"
  | Arith (op, xs) ->
    Printf.eprintf "( %s ) " (string_of_arithop op);
    print_ses xs
  | Rel (rel, xs) ->
    Printf.eprintf "( %s ) " (string_of_relop rel);
    print_ses xs
  | Union l -> print_se_list_with_separator l "∪"
  | Inter l -> print_se_list_with_separator l "∩"
  | Diff (x, y) ->
    prerr_string "(";
    print_se x;
    prerr_string ")-(";
    print_se y;
    prerr_string ")"
  | Cond (x, y) ->
    prerr_string "if (";
    print_se x;
    prerr_string ")=∅ then (";
    print_se y;
    prerr_string ") else ∅"

and print_ses (xs : unit se list) =
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
    prerr_string "(";
    print_se arr.(!i);
    prerr_string ")";
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
      let se_list = SESet.elements se in
      print_se (union_of_list se_list);
      prerr_newline ())
    var_to_se

let show_sc_tbl (tbl : (unit se, SESet.t) Hashtbl.t) =
  Hashtbl.iter
    (fun key data ->
      prerr_string "insensitive_sc :\n";
      print_se key;
      (match key with
      | Fld (_, _) -> prerr_string " <- "
      | _ -> prerr_string " = ");
      let se_list = SESet.elements data in
      print_se (Union se_list);
      prerr_newline ())
    tbl

let print_sc_info () =
  show_var_se_tbl var_to_se;
  show_sc_tbl insensitive_sc
