type expr_summary = {
  exp_type : CL.Types.type_expr;
  exp_loc : CL.Location.t;
  exp_context : string;
}

type mod_summary = {
  mod_type : CL.Types.module_type;
  mod_loc : CL.Location.t;
  mod_context : string;
}

type code_loc =
  | Expr_loc of expr_summary
  | Mod_loc of mod_summary
  | Bop_loc of CL.Types.value_description

and param = (CL.Ident.t * string) option
and arg = value se option list

and _ expr =
  | Expr_var : (CL.Ident.t * string) -> param expr
  | Expr : loc -> loc expr

and arr = Static of loc list | Dynamic of loc

and _ tagged_expr =
  | Val : 'a expr -> 'a tagged_expr
  | Packet : 'a expr -> 'a tagged_expr

and ctor = string option
and fld = ctor * int option

and arith =
  | ADD
  | SUB
  | DIV
  | MUL
  | NEG
  | ABS
  | MOD
  | AND
  | OR
  | NOT
  | XOR
  | LSL
  | LSR
  | ASR
  | SUCC
  | PRED

and rel = EQ | NE | LT | LE | GT | GE

and arithop =
  | INT of arith
  | INT32 of arith
  | INT64 of arith
  | FLOAT of arith
  | NATURALINT of arith

and relop = GEN of rel
and pattern
and value
and loc = int * string

and _ se =
  | Top : _ se
  | Const : CL.Asttypes.constant -> _ se
  | Prim : CL.Primitive.description -> value se
  | Fn : param * loc expr list -> value se
  | Var : _ tagged_expr -> _ se
  | App_V : value se * arg -> value se
  | App_P : value se * arg -> value se
  | Ctor : ctor * arr -> value se
  | Ctor_pat : ctor * pattern se list -> pattern se
  | Fld : value se * fld -> value se
  | Arith : arithop * value se list -> value se
  | Rel : relop * value se list -> value se
  | Diff : value se * pattern se -> value se
  | Loc : loc * pattern se option -> pattern se

val current_module : string ref
val new_memory : string -> loc
val new_temp_var : string -> param expr
val hash : 'a -> int

module SESet : Set.S with type elt = value se

module Worklist : sig
  type t = (int, unit) Efficient_hashtbl.t

  val add : int -> t -> unit
  val mem : int -> t -> bool
  val prepare_step : t -> t -> unit
end

val new_array : int -> loc array
val loc_of_summary : code_loc -> loc
val loc_of_mod : CL.Typedtree.module_expr -> loc
val expr_of_mod : CL.Typedtree.module_expr -> loc expr
val val_of_mod : CL.Typedtree.module_expr -> value se
val packet_of_mod : CL.Typedtree.module_expr -> value se
val loc_of_expr : CL.Typedtree.expression -> loc
val expr_of_expr : CL.Typedtree.expression -> loc expr
val val_of_expr : CL.Typedtree.expression -> value se
val packet_of_expr : CL.Typedtree.expression -> value se
val linking : bool ref
val worklist : Worklist.t
val sc : (string, (value se, SESet.t) Efficient_hashtbl.t) Efficient_hashtbl.t
val lookup_sc : value se -> SESet.t
val update_sc : value se -> SESet.elt list -> unit
val memory : (string, (loc, SESet.t) Efficient_hashtbl.t) Efficient_hashtbl.t
val lookup_mem : loc -> SESet.t
val update_mem : loc -> SESet.elt list -> unit

type var_se_tbl =
  (string, (CL.Ident.t, SESet.t) Efficient_hashtbl.t) Efficient_hashtbl.t

val var_to_se : var_se_tbl
val update_var : CL.Ident.t -> SESet.elt list -> unit
val se_of_var : CL.Ident.t -> string -> SESet.elt list

type to_be_resolved = (loc, CL.Path.t * string) Efficient_hashtbl.t

val to_be_resolved : to_be_resolved
val update_to_be : loc -> CL.Path.t -> unit
val label_to_summary : (loc, code_loc) Efficient_hashtbl.t
val list_to_array : 'a list -> 'a array

(* for resolution *)
val changed : bool ref
val prev_worklist : Worklist.t
val exn_of_file : (string, value se list) Efficient_hashtbl.t

module GESet : Set.S with type elt = pattern se

val update_exn_of_file : string -> value se list -> unit
val update_c : value se -> SESet.t -> bool
val update_loc : loc -> SESet.t -> bool
val grammar : (pattern se, GESet.t) Efficient_hashtbl.t
val update_g : 'a tagged_expr -> GESet.t -> bool
val abs_mem : (loc, GESet.t) Efficient_hashtbl.t
val update_abs_loc : loc -> GESet.t -> bool
