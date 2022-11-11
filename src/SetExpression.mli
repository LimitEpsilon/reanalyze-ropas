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
  | Expr : code_loc -> code_loc expr

and arr = Static of loc array | Dynamic of loc

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
  | Fn : param * code_loc expr list -> value se
  | Var : _ tagged_expr -> _ se
  | App_V : value se * arg -> value se
  | App_P : value se * arg -> value se
  | Ctor : ctor * arr -> value se
  | Ctor_pat : ctor * pattern se array -> pattern se
  | Fld : value se * fld -> value se
  | Arith : arithop * value se list -> value se
  | Rel : relop * value se list -> value se
  | Diff : value se * pattern se -> value se
  | Loc : loc * pattern se option -> pattern se

val current_module : string ref
val new_memory : string -> loc
val new_temp_var : string -> param expr
val hash : 'a -> int

module SESet : sig
  type t = (value se, unit) Hashtbl.t
  exception Not_empty

  val mem : value se -> t -> bool

  val add : value se -> t -> unit

  val diff : t -> t -> t

  val union : t -> t -> t

  val empty : unit -> t

  val is_empty : t -> bool

  val iter : (value se -> unit) -> t -> unit

  val of_list : value se list -> t

  val singleton : value se -> t

  val elements : t -> value se list

  val filter : (value se -> bool) -> t -> t
end


module Worklist : sig
  type t = (int, unit) Hashtbl.t

  val add : int -> t -> unit
  val mem : int -> t -> bool
  val prepare_step : t -> t -> unit
end

val worklist : Worklist.t
val current_file : (CL.Ident.t, SESet.t) Hashtbl.t ref
val sc : (value se, SESet.t) Hashtbl.t
val update_sc : value se -> value se list -> unit
val mem : (loc, SESet.t) Hashtbl.t

type var_se_tbl = (CL.Ident.t, SESet.t) Hashtbl.t

val var_to_se : var_se_tbl
val update_var : CL.Ident.t -> value se list -> unit

type to_be_resolved = (code_loc, CL.Path.t * string) Hashtbl.t

val to_be_resolved : to_be_resolved
val update_to_be : code_loc -> CL.Path.t -> unit

(* val list_rev_to_array : 'a list -> 'a -> 'a array *)
(* val list_to_array : 'a list -> 'a -> 'a array *)
val val_of_expr : CL.Typedtree.expression -> value se
val packet_of_expr : CL.Typedtree.expression -> value se
val val_of_mod : CL.Typedtree.module_expr -> value se
val packet_of_mod : CL.Typedtree.module_expr -> value se
val se_of_var : CL.Ident.t -> value se list
val se_of_mb : CL.Typedtree.module_binding -> value se list * value se list
val se_of_vb : CL.Typedtree.value_binding -> value se list * value se list

val se_of_struct_item :
  CL.Typedtree.structure_item -> value se list * value se list

val se_of_struct : CL.Typedtree.structure -> value se list * value se list

val se_of_module_expr :
  CL.Typedtree.module_expr -> value se list * value se list

(* val extract :
 *   'a CL.Typedtree.case ->
 *   ('a CL.Typedtree.general_pattern * bool) * CL.Typedtree.expression *)

val se_of_expr : CL.Typedtree.expression -> value se list * value se list

(* for resolution *)
val changed : bool ref
val prev_worklist : Worklist.t
val exn_of_file : (string, value se list) Hashtbl.t

module GESet : Set.S with type elt = pattern se

val update_exn_of_file : string -> value se list -> unit
val update_c : value se -> SESet.t -> bool
val update_loc : loc -> SESet.t -> bool
val grammar : (pattern se, GESet.t) Hashtbl.t
val update_g : 'a tagged_expr -> GESet.t -> bool
val abs_mem : (loc, GESet.t) Hashtbl.t
val update_abs_loc : loc -> GESet.t -> bool
