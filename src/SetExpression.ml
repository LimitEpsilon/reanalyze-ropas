[%%import "../config.h"]

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

(* construct : Types.cstr_name, Some Types.cstr_loc *)
(* variant : Asttypes.label *)
and ctor = (string * code_loc option) option

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

and relop = GEN of rel

(* set expression type *)
and _ se =
  | Bot : _ se (* empty set *)
  | Top : _ se (* _ *)
  | Const : CL.Asttypes.constant -> _ se
  | Mem : int -> _ se (* memory location, +\alpha to constructors *)
  | Prim :
      CL.Primitive.description
      -> _ se (* primitives, later converted to arith/rel/fld/mem *)
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

let address = ref 0

let new_memory () : 'a se =
  let mem = Mem !address in
  address := !address + 1;
  mem

let print_loc loc =
  CL.Location.print_loc Format.str_formatter loc;
  prerr_string (Format.flush_str_formatter ())

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
    print_loc loc;
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
  | Mem n ->
    prerr_string "(Mem ";
    prerr_int n;
    prerr_string ")"
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
  | Prim {prim_name} -> prerr_string ("Prim (" ^ prim_name ^ ")")
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
    (match k with None -> prerr_string " " | Some (s, _) -> prerr_string s);
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
      | hd :: tl ->
        prerr_string "(";
        print_se hd;
        prerr_string ")";
        if tl != [] then prerr_string "|";
        l' := tl
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
let se_of_int n = Const (CL.Asttypes.Const_int n)

let union_of_list l =
  let make_union acc se =
    match acc with
    | Bot -> se
    | _ -> ( match se with Bot -> acc | _ -> Union (acc, se))
  in
  List.fold_left make_union Bot l

let se_of_var x =
  let se_list =
    try SESet.elements (CL.Ident.Tbl.find var_to_se x) with _ -> []
  in
  Or se_list

let val_of_loc loc = Var (Val (Expr loc))
let packet_of_loc loc = Var (Packet (Expr loc))

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
  | Lident s -> s
  | Ldot (li, s) -> string_of_longident li ^ "." ^ s
  | Lapply (l1, l2) ->
    (* applicative functor : see ocamlc -help | grep app-funct *)
    string_of_longident l1 ^ "(" ^ string_of_longident l2 ^ ")"

let string_of_typ : Types.type_desc -> string = function
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

let se_of_functor (m : CL.Typedtree.module_expr) =
  match m.mod_desc with
  | ((Tmod_functor (Named (Some x, {txt = Some s; loc}, _), me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_var (x, {txt = s; loc});
        pat_loc = loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    Fn ([pat], [Expr me.mod_loc])
  | ((Tmod_functor (Named (Some x, {txt = None; loc}, _), me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_var (x, {txt = ""; loc});
        pat_loc = loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    Fn ([pat], [Expr me.mod_loc])
  | ((Tmod_functor (Unit, me))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    let loc = CL.Location.mknoloc () in
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_any;
        pat_loc = loc.loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    Fn ([pat], [Expr me.mod_loc])
  | ((Tmod_functor (x, loc, _, me))
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    let pat : CL.Typedtree.pattern =
      {
        pat_desc = Tpat_var (x, loc);
        pat_loc = loc.loc;
        pat_extra = [];
        pat_type = CL.Btype.newgenvar ();
        pat_env = m.mod_env;
        pat_attributes = [];
      }
    in
    Fn ([pat], [Expr me.mod_loc])
  | _ -> failwith "Oops, not a functor but called se_of_functor"

let se_of_mb (mb : CL.Typedtree.module_binding) =
  match mb with
  | ({mb_id = Some id; mb_expr = {mod_loc}}
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    [Ctor (Some (CL.Ident.name id, None), [val_of_loc mod_loc])]
  | ({mb_id; mb_expr = {mod_loc}}
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    [Ctor (Some (CL.Ident.name mb_id, None), [val_of_loc mod_loc])]
  | _ -> []

(* a structure_item may bind multiple names, make a list of all possible constructs *)
let se_of_struct_item (str_item : CL.Typedtree.structure_item) =
  match str_item.str_desc with
  | Tstr_value (_, vbs) ->
    (* correlate the name of the value binding to the list of set expressions it is bound to *)
    let local_value_name_tbl = Hashtbl.create 1 in
    (* update the table *)
    let update_tbl key data =
      if Hashtbl.mem local_value_name_tbl key then (
        let original = Hashtbl.find local_value_name_tbl key in
        Hashtbl.remove local_value_name_tbl key;
        Hashtbl.add local_value_name_tbl key (data :: original))
      else Hashtbl.add local_value_name_tbl key [data]
    in
    (* update the table while traversing the pattern *)
    let rec solveEq (pat : CL.Typedtree.pattern) se =
      match pat.pat_desc with
      | Tpat_any | Tpat_constant _ -> ()
      | Tpat_var (x, _) -> update_tbl (CL.Ident.name x) se
      | Tpat_alias (p, a, _) ->
        update_tbl (CL.Ident.name a) se;
        solveEq p se
      | Tpat_tuple list -> solveCtor None se list
      | ((Tpat_construct (_, {cstr_name; cstr_loc}, list, _))
      [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
        solveCtor (Some (cstr_name, Some cstr_loc)) se list
      | ((Tpat_construct (_, {cstr_name; cstr_loc}, list))
      [@if ocaml_version < (4, 13, 0) || defined npm]) ->
        solveCtor (Some (cstr_name, Some cstr_loc)) se list
      | Tpat_variant (lbl, p_o, _) -> (
        let constructor = Some (lbl, None) in
        match p_o with
        | None -> ()
        | Some p -> solveEq p (Fld (se, (constructor, se_of_int 1))))
      | Tpat_record (key_val_list, _) ->
        let list =
          List.map
            (fun (_, lbl, pat) -> (lbl.CL.Types.lbl_pos, pat))
            key_val_list
        in
        solveRec se list
      | Tpat_array list -> solveCtor None se list
      | Tpat_lazy p -> solveEq p (App_V (se, []))
      | Tpat_or (lhs, rhs, _) ->
        solveEq lhs se;
        solveEq rhs se
    and solveCtor constructor se list =
      let l = ref list in
      let i = ref 0 in
      while !l != [] do
        (match !l with
        | hd :: tl ->
          solveEq hd (Fld (se, (constructor, se_of_int !i)));
          l := tl
        | _ -> assert false);
        i := !i + 1
      done
    and solveRec se list =
      let l = ref list in
      while !l != [] do
        match !l with
        | hd :: tl ->
          let i, p = hd in
          solveEq p (Fld (se, (None, se_of_int i)));
          l := tl
        | _ -> assert false
      done
    in
    let se_of_vb ({vb_pat; vb_expr = {exp_loc}} : CL.Typedtree.value_binding) =
      solveEq vb_pat (val_of_loc exp_loc);
      let seq_of_ctors = Hashtbl.to_seq local_value_name_tbl in
      let acc_ctors acc (name, or_list) =
        Ctor (Some (name, None), [Or or_list]) :: acc
      in
      Seq.fold_left acc_ctors [] seq_of_ctors
    in
    List.flatten (List.map se_of_vb vbs)
  | Tstr_module mb -> se_of_mb mb
  | Tstr_recmodule mbs ->
    List.flatten (List.map se_of_mb mbs)
  | Tstr_include {incl_mod = {mod_loc}} -> [val_of_loc mod_loc]
  | _ -> []

(* a struct is a union of constructs *)
let se_of_struct (str : CL.Typedtree.structure) =
  let item_list = List.map se_of_struct_item str.str_items in
  union_of_list (List.flatten item_list)

exception Not_resolvable

let resolve_as_const : unit se -> CL.Asttypes.constant = function
  | Arith (INT ADD, [_; _]) -> Const_char 'c'
  | Arith (INT SUB, [_; _]) -> Const_float "1.0"
  | Arith (INT DIV, [_; _]) -> Const_int 1
  | Arith (INT MUL, [_; _]) -> Const_int32 1l
  | Arith (INT NEG, [_; _]) -> Const_int64 2L
  | Arith (FLOAT ABS, [_]) (* absolute value *) | Arith (INT MOD, [_; _]) ->
    Const_nativeint 0n
  | Arith (INT AND, [_; _])
  | Arith (INT OR, [_; _])
  | Arith (INT NOT, [_; _])
  | Arith (INT XOR, [_; _])
  | Arith (INT LSL, [_; _]) (* <<, logical *)
  | Arith (INT LSR, [_; _]) (* >>, logical *)
  | Arith (INT ASR, [_; _]) ->
    Const_int 1 (* >>, arithmetic sign extension *)
  | Arith (INT SUCC, [_]) (* ++x *) | Arith (INT PRED, [_]) ->
    Const_int 1 (* --x *)
  | _ -> Const_int 1

let resolve_arith : unit se -> unit se =
 fun e -> try Const (resolve_as_const e) with Not_resolvable -> Top
