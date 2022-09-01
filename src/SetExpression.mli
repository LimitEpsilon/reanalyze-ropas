type code_loc = CL.Location.t
and param = code_loc list
and 'a arg = 'a se option list
and _ expr = Expr_var : param -> param expr | Expr : code_loc -> code_loc expr

and _ tagged_expr =
  | Val : 'a expr -> 'a tagged_expr
  | Packet : 'a expr -> 'a tagged_expr

and env = Env_var | Env of (param * code_loc tagged_expr) list
and ctor = (string * code_loc option) option
and 'a fld = ctor * 'a se

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

and _ se =
  | Top : 'b se
  | Const : CL.Asttypes.constant -> 'c se
  | Prim : CL.Primitive.description -> 'd se
  | Fn : param * code_loc expr list -> unit se
  | Closure : param * code_loc expr list * env -> env se
  | Var : 'e tagged_expr -> unit se
  | Var_sigma : code_loc tagged_expr * env -> env se
  | App_V : 'a se * 'a arg -> 'a se
  | App_P : 'a se * 'a arg -> 'a se
  | Ctor : ctor * 'a se array option * int option -> 'a se
  | Fld : 'a se * 'a fld -> 'a se
  | Arith : arithop * 'a se list -> 'a se
  | Rel : relop * 'a se list -> 'a se
  | Union : 'a se list -> 'a se
  | Inter : 'a se list -> 'a se
  | Diff : 'a se * 'a se -> 'a se
  | Cond : 'a se * 'a se -> 'a se

and rule =
  [ `APP
  | `ARITH
  | `CASE
  | `CON
  | `EXTERN
  | `FIELD
  | `FN
  | `FOR
  | `FORCE
  | `HANDLE
  | `IDENTITY
  | `IGNORE
  | `LET
  | `OP
  | `RAISE
  | `REL
  | `SEQ
  | `SETFIELD
  | `VAR
  | `WHILE ]

val address : int ref
val new_memory : unit -> int

module SE : sig
  type t = unit se

  val compare : 'a -> 'a -> int
end

module SESet : Set.S with type elt = SE.t

val insensitive_sc : (unit se, SESet.t) Hashtbl.t
val sensitive_sc : (env se, env se list) Hashtbl.t
val update_sc : unit se -> SESet.elt -> unit

type var_se_tbl = (CL.Ident.t, SESet.t) Hashtbl.t

val var_to_se : var_se_tbl
val update_var : CL.Ident.t -> SESet.elt -> unit

type to_be_resolved = (code_loc, CL.Path.t) Hashtbl.t

val to_be_resolved : to_be_resolved
val update_to_be : code_loc -> CL.Path.t -> unit
val union_of_list : 'a se list -> 'a se

(* val list_rev_to_array : 'a list -> 'a -> 'a array *)
(* val list_to_array : 'a list -> 'a -> 'a array *)
val se_of_int : int -> 'a se
val se_of_var : CL.Ident.t -> unit se
val val_of_loc : code_loc -> unit se
val packet_of_loc : code_loc -> unit se
val se_of_mb : CL.Typedtree.module_binding -> unit se * unit se
val se_of_vb : CL.Typedtree.value_binding -> unit se * unit se
val se_of_struct_item : CL.Typedtree.structure_item -> unit se * unit se
val se_of_struct : CL.Typedtree.structure -> unit se * unit se
val se_of_module_expr : CL.Typedtree.module_expr -> unit se * unit se

(* val extract :
 *   'a CL.Typedtree.case ->
 *   ('a CL.Typedtree.general_pattern * bool) * CL.Typedtree.expression *)

val se_of_expr : CL.Typedtree.expression -> unit se * unit se
