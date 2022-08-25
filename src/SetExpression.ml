type param = CL.Typedtree.pattern list
and arg = code_loc expr option list
and code_loc = CL.Location.t

and _ expr =
  | Expr_var : param -> param expr
  | Expr : code_loc -> code_loc expr
  | Extern :
      string * CL.Types.type_desc
      -> code_loc expr (* blackbox, includes I/O *)

and _ tagged_expr =
  | Val : 'a expr -> 'a tagged_expr
  | Packet : 'a expr -> 'a tagged_expr

and env = Env_var | Env of (param * code_loc tagged_expr) list

(* construct : name |> string_of_longident *)
(* variant : CL.Asttypes.label *)
and ctor = string option

(* construct : need to know arity *)
(* record : translate field name to position(int, starts from 0) *)
and 'a fld = ctor * 'a se

(* CL.Types.value_description.value_kind | Val_prim of {prim_name : string ;} *)
and arith =
  | ADD
  | SUB
  | DIV
  | MUL
  | NEG
  | ABS (* absolute value *)
  | MOD
  | AND
  | OR
  | NOT
  | XOR
  | LSL (* <<, logical *)
  | LSR (* >>, logical *)
  | ASR (* >>, arithmetic sign extension *)
  | SUCC (* ++x *)
  | PRED (* --x *)

and rel =
  | EQ (* == *)
  | NE (* != *)
  | LT (* < *)
  | LE (* <= *)
  | GT (* > *)
  | GE (* >= *)

and arithop =
  | INT of arith
  | INT32 of arith
  | INT64 of arith
  | FLOAT of arith
  | NATURALINT of arith

and relop =
  | GEN of rel

(* set expression type *)
and _ se =
  | Bot : _ se (* empty set *)
  | Top : _ se (* _ *)
  | Const : CL.Asttypes.constant -> _ se
  | Mem : int -> _ se (* memory location, +\alpha to constructors *)
  | Prim : string -> _ se (* primitives, later converted to arith/rel/fld/mem *)
  | Fn : param * code_loc expr list -> unit se (* context-insensitive *)
  | Closure :
      param * code_loc expr list * env
      -> env se (* lambda (p->e)+ / lazy when param = nil *)
  | Var : _ tagged_expr -> unit se (* set variable, context-insensitive *)
  | Var_sigma : code_loc tagged_expr * env -> env se (* set variable *)
  | App_V : 'a se * arg -> 'a se (* possible values / force when arg = nil *)
  | App_P :
      'a se * arg
      -> 'a se (* possible exn packets / force when arg = nil *)
  | Ctor : ctor * 'a se list -> 'a se (* construct / record field *)
  | Fld : 'a se * 'a fld -> 'a se (* field of a record / deconstruct *)
  | Arith : arithop * 'a se list -> 'a se (* arithmetic operators *)
  | Rel : relop * 'a se list -> 'a se (* relation operators *)
  | Union : 'a se * 'a se -> 'a se (* union *)
  | Inter : 'a se * 'a se -> 'a se (* intersection *)
  | Diff : 'a se * 'a se -> 'a se (* difference *)
  | Or : 'a se list -> 'a se (* A|B : A or B, but not both. *)
  | Cond : 'a se * 'a se -> 'a se (* conditional set expression *)

(* divide_by_zero : check denominator, if constant check if zero.          *)
(*                : if identifier look up in var_to_se to check if constant*)
(*                : if constant check if zero, else mark might_raise       *)
and rule =
  [ `APP
  | `FORCE
  | `IGNORE
  | `IDENTITY
  | `ARITH
  | `REL
  | `EXTERN
  | `FN
  | `VAR
  | `LET
  | `OP
  | `CON
  | `FIELD
  | `SETFIELD
  | `SEQ
  | `CASE
  | `HANDLE
  | `RAISE
  | `FOR
  | `WHILE ]

let string_of_arithop : arithop -> string = function
  INT x | INT32 x | INT64 x | FLOAT x | NATURALINT x ->
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
  | PRED -> "--"

let string_of_relop : relop -> string = function GEN x ->
  match x with
  | EQ -> "=="
  | NE -> "!="
  | LT -> "<"
  | LE -> "<="
  | GT -> ">"
  | GE -> ">="

let address = ref 0

let new_memory () : 'a se=
  let mem = Mem !address in
  address := !address + 1;
  mem

let print_param par =
  prerr_string "[";
  let print_pattern pat =
    CL.Printpat.pretty_pat pat;
    prerr_string "; "
  in
  List.iter print_pattern par;
  prerr_string "]"

let print_expr : type k. k expr -> unit = function
  | Expr_var p ->
    prerr_string "Expr_var (";
    print_param p;
    prerr_string ")"
  | Expr loc ->
    prerr_string "Expr (";
    CL.Location.print_loc Format.str_formatter loc;
    prerr_string (Format.flush_str_formatter ());
    prerr_string ")"
  | Extern (s, _) ->
    prerr_string "Extern (";
    prerr_string s;
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
  | Bot -> prerr_string "⊥"
  | Top -> prerr_string "⊤"
  | Const c -> prerr_string (CL.Printpat.pretty_const c)
  | Mem n -> prerr_string "(Mem "; prerr_int n; prerr_string ")"
  | Fn (p, list) ->
    prerr_string "<";
    print_param p;
    prerr_string "-> [";
    List.iter
      (fun e ->
        print_expr e;
        prerr_string ";")
      list;
    prerr_string "]>"
  | Var e ->
    prerr_string "X (";
    print_tagged_expr e;
    prerr_string ")"
  | App_V (se, list) ->
    prerr_string "AppV (";
    print_se se;
    prerr_string ", [";
    List.iter
      (fun o ->
        (match o with None -> prerr_string " " | Some e -> print_expr e);
        prerr_string ";")
      list;
    prerr_string "])"
  | App_P (se, list) ->
    prerr_string "AppP (";
    print_se se;
    prerr_string ", [";
    List.iter
      (fun o ->
        (match o with None -> prerr_string " " | Some e -> print_expr e);
        prerr_string ";")
      list;
    prerr_string "])"
  | Ctor (k, list) ->
    prerr_string "Con (";
    (match k with None -> prerr_string " " | Some s -> prerr_string s);
    prerr_string ", [";
    List.iter
      (fun se ->
        print_se se;
        prerr_string ";")
      list;
    prerr_string "])"
  | Fld (se, lbl) ->
    prerr_string "Fld (";
    print_se se;
    prerr_string ", (";
    (match lbl with
    | None, x ->
      prerr_string " , ";
      print_se x
    | Some s, x ->
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
  | Union (x, y) ->
    prerr_string "(";
    print_se x;
    prerr_string ")∪(";
    print_se y;
    prerr_string ")"
  | Inter (x, y) ->
    prerr_string "(";
    print_se x;
    prerr_string ")∩(";
    print_se y;
    prerr_string ")"
  | Or l ->
    let l' = ref l in
    while !l' != [] do
      match !l' with
      | hd :: tl -> (prerr_string "("; print_se hd; prerr_string ")"; if tl != [] then prerr_string "|"; l' := tl)
      | _ -> assert false
    done
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

module SE = struct
  type t = unit se

  let compare = compare
end

module SESet = Set.Make (SE)

let insensitive_sc : (unit se, unit se) Hashtbl.t = Hashtbl.create 256
let sensitive_sc : (env se, env se) Hashtbl.t = Hashtbl.create 256

type globalenv = (param, code_loc tagged_expr) Hashtbl.t

let show_env_map (env_map : globalenv) =
  Hashtbl.iter
    (fun param loc_tagged_expr ->
      prerr_string "Globalenv :\n param = ";
      print_param param;
      prerr_string "\n code_loc tagged_expr = ";
      print_tagged_expr loc_tagged_expr;
      prerr_newline ())
    env_map

let globalenv : globalenv = Hashtbl.create 256

type var_se_tbl = SESet.t CL.Ident.Tbl.t

let var_to_se : var_se_tbl = CL.Ident.Tbl.create 256

let union_of_list l =
  let make_union acc se =
    match acc with
    | Bot -> se
    | _ -> (match se with Bot -> acc | _ -> Union (acc, se))
  in
  List.fold_left make_union Bot l

let se_of_var x =
  let se_list =
    try SESet.elements (CL.Ident.Tbl.find var_to_se x) with _ -> []
  in
  Or se_list

let show_var_se_tbl (var_to_se : var_se_tbl) =
  CL.Ident.(
    Tbl.iter
      (fun x se ->
        prerr_string "var_to_se :\n ident = ";
        prerr_string (unique_name x);
        prerr_string "\n se = ";
        let se_list = SESet.elements se in
        print_se (union_of_list se_list);
        prerr_newline ())
      var_to_se)

let undetermined_var : var_se_tbl = CL.Ident.Tbl.create 64

(* from https://github.com/ocaml/ocaml/blob/1e52236624bad1c80b3c46857723a35c43974297/ocamldoc/odoc_misc.ml#L83 *)
let rec string_of_longident : CL.Longident.t -> string = function
  | CL.Longident.Lident s -> s
  | CL.Longident.Ldot (li, s) -> string_of_longident li ^ "." ^ s
  | CL.Longident.Lapply (l1, l2) ->
    (* applicative functor : see ocamlc -help | grep app-funct *)
    string_of_longident l1 ^ "(" ^ string_of_longident l2 ^ ")"

let string_of_typ : CL.Types.type_desc -> string = function
  | Tvar _ -> "var"
  | Tarrow _ -> "function"
  | Ttuple _ -> "tuple"
  | Tconstr _ -> "construct"
  | Tobject _ -> "object"
  | Tfield _ -> "field"
  | Tnil -> "nil"
  | Tlink _ -> "link"
  | Tsubst _ -> "subst"
  | Tvariant _ -> "variant"
  | Tunivar _ -> "univar"
  | Tpoly _ -> "poly"
  | Tpackage _ -> "package"

exception Not_resolvable

let resolve_as_const : unit se -> CL.Asttypes.constant = function
  | Arith (INT ADD, [x; y]) -> Const_char 'c'
  | Arith (FLOAT ADD, [x; y]) -> Const_float "1.0"
  | Arith (INT DIV, [x; y]) -> Const_int 1
  | Arith (INT MUL, [x; y]) -> Const_int32 1l
  | Arith (INT SUCC, [x]) -> Const_int64 2L
  | Arith (INT SUB, [x; y]) -> Const_nativeint 0n
  | Arith (INT ADD, [x; y])
  | Arith (INT SUB, [x; y])
  | Arith (INT DIV, [x; y])
  | Arith (INT MUL, [x; y])
  | Arith (INT NEG, [x; y])
  | Arith (FLOAT ABS, [x; y]) (* absolute value *)
  | Arith (INT MOD, [x; y])
  | Arith (INT AND, [x; y])
  | Arith (INT OR, [x; y])
  | Arith (INT NOT, [x; y])
  | Arith (INT XOR, [x; y])
  | Arith (INT LSL, [x; y]) (* <<, logical *)
  | Arith (INT LSR, [x; y]) (* >>, logical *)
  | Arith (INT ASR, [x; y]) -> Const_int 1 (* >>, arithmetic sign extension *)
  | Arith (INT SUCC, [x]) (* ++x *)
  | Arith (INT PRED, [x]) -> Const_int 1 (* --x *)

let resolve_arith : unit se -> unit se = fun e ->
  try Const (resolve_as_const e) with
  | Not_resolvable -> Top
