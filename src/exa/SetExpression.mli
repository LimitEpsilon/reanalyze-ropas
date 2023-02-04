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
  | Temp

and loc = int * string
and tagged_expr = Val of loc | Packet of loc
and id = CL.Ident.t * string
and param = id option
and arg = tagged_expr option list
and ctor = string option
and fld = ctor * int option
and pattern
and value

and _ se =
  | Top : _ se
  | Const : CL.Asttypes.constant -> _ se
  | Ctor_pat : ctor * pattern se list -> pattern se
  | Var : tagged_expr -> value se
  | Loc : loc -> value se
  | Id : id -> value se
  | Prim : CL.Primitive.description -> value se
  | Fn : param * loc list -> value se
  | App_v : tagged_expr * arg -> value se
  | Prim_v : CL.Primitive.description * arg -> value se
  | App_p : tagged_expr * arg -> value se
  | Prim_p : CL.Primitive.description * arg -> value se
  | Ctor : ctor * loc list -> value se
  | Arr : loc -> value se
  | Fld : tagged_expr * fld -> value se
  | Diff : tagged_expr * pattern se -> value se

module LocSet : Set.S with type elt = loc

val current_module : string ref
val new_memory : string -> loc
val new_temp_var : string -> tagged_expr
val new_array : int -> loc array
val loc_of_summary : code_loc -> loc
val loc_of_mod : CL.Typedtree.module_expr -> loc
val val_of_mod : CL.Typedtree.module_expr -> tagged_expr
val packet_of_mod : CL.Typedtree.module_expr -> tagged_expr
val loc_of_expr : CL.Typedtree.expression -> loc
val val_of_expr : CL.Typedtree.expression -> tagged_expr
val packet_of_expr : CL.Typedtree.expression -> tagged_expr
val val_of_path : CL.Path.t -> tagged_expr

module SESet : Set.S with type elt = value se

module Worklist : sig
  type t = SESet.t ref

  val add : SESet.elt -> t -> unit
  val mem : SESet.elt -> t -> bool
  val prepare_step : t -> t -> unit
end

module SEnv : sig
  module Internal : Map.S with type key = id

  type t = tagged_expr Internal.t

  val compare : t -> t -> int

  exception Inconsistent

  val union : t -> t -> t
end

module Cstr : Map.S with type key = SEnv.t

val cstr_union : SESet.t Cstr.t -> SESet.t Cstr.t -> SESet.t Cstr.t
val worklist : Worklist.t
val prev_worklist : Worklist.t
val sc : (value se, SESet.t Cstr.t) Hashtbl.t
val reverse_sc : (value se, SESet.t) Hashtbl.t
val lookup_sc : value se -> SESet.t Cstr.t
val update_worklist : value se -> SESet.t -> unit
val update_sc : value se -> SESet.t Cstr.t -> unit
val get_context : value se -> string
val init_sc : value se -> value se list -> unit

type var_se_tbl = (string, (CL.Ident.t, tagged_expr) Hashtbl.t) Hashtbl.t

val global_env : var_se_tbl
val unresolved_ids : (CL.Ident.t, unit) Hashtbl.t
val init_id : CL.Ident.t -> tagged_expr -> unit
val lookup_id : id -> tagged_expr
val label_to_summary : (loc, code_loc) Hashtbl.t
val list_to_array : 'a list -> 'a array

(* for resolution *)
val changed : bool ref
val exn_of_file : (string, value se list) Hashtbl.t
val update_exn_of_file : string -> value se list -> unit
