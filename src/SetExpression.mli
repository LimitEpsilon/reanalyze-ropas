type code_loc =
  | Expr_loc of CL.Typedtree.expression
  | Mod_loc of CL.Typedtree.module_expr
  | Bop_loc of CL.Types.value_description

and param = CL.Ident.t option
and arg = value se option list

and _ expr =
  | Expr_var : CL.Ident.t -> param expr
  | Expr : code_loc -> code_loc expr

and arr = Static of int array | Dynamic of int

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
  | Loc : int * pattern se option -> pattern se

(* val address : int ref *)
val new_memory : unit -> int
val new_temp_var : unit -> param expr

module SESet : Set.S with type elt = value se

val current_file : (Ident.t, SESet.t) Hashtbl.t ref
val sc : (value se, SESet.t) Hashtbl.t
val update_sc : value se -> SESet.elt list -> unit
val mem : (int, SESet.t) Hashtbl.t

type var_se_tbl = (CL.Ident.t, SESet.t) Hashtbl.t

val var_to_se : var_se_tbl
val update_var : CL.Ident.t -> SESet.elt list -> unit

type to_be_resolved = (code_loc, CL.Path.t) Hashtbl.t

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
val exn_of_file : (string, value se list) Hashtbl.t

module GESet : Set.S with type elt = pattern se

val update_exn_of_file : string -> value se list -> unit
val update_c : value se -> SESet.t -> unit
val update_loc : int -> SESet.t -> unit

val grammar : (pattern se, GESet.t) Hashtbl.t
val update_g : pattern se -> GESet.t -> unit

val abs_mem : (int, GESet.t) Hashtbl.t
val update_abs_loc : int -> GESet.t -> unit
