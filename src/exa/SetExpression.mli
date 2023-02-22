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

and se =
  | Top  (** _ *)
  | Const of CL.Asttypes.constant
  | Var of tagged_expr  (** set variable *)
  | Loc of loc  (** !ℓ *)
  | Id of id  (** identifiers *)
  | Prim of CL.Primitive.description
      (** primitives, later converted to top/fld/arr/ctor *)
  | Fn of param * loc list  (** lambda expression *)
  | App_v of tagged_expr * arg  (** possible values / force when arg = nil *)
  | Prim_v of CL.Primitive.description * arg
  | App_p of tagged_expr * arg
      (** possible exn packets / force when arg = nil *)
  | Prim_p of CL.Primitive.description * arg
  | Ctor of ctor * loc list  (** One ADT to rule them all :D *)
  | Arr of loc  (** Dynamically allocated arrays *)
  | Fld of tagged_expr * fld  (** field of a record / deconstruct *)

module LocSet : Set.S with type elt = loc

val current_module : string ref
val new_memory : string -> loc
val new_temp_var : unit -> tagged_expr
val new_array : int -> loc array
val loc_of_summary : code_loc -> loc
val loc_of_mod : CL.Typedtree.module_expr -> loc
val val_of_mod : CL.Typedtree.module_expr -> tagged_expr
val packet_of_mod : CL.Typedtree.module_expr -> tagged_expr
val loc_of_expr : CL.Typedtree.expression -> loc
val val_of_expr : CL.Typedtree.expression -> tagged_expr
val packet_of_expr : CL.Typedtree.expression -> tagged_expr
val val_of_path : CL.Path.t -> tagged_expr

module SESet : Set.S with type elt = se

module Worklist : sig
  type t = SESet.t ref

  val add : SESet.elt -> t -> unit
  val mem : SESet.elt -> t -> bool
  val prepare_step : t -> t -> unit
end

val worklist : Worklist.t
val prev_worklist : Worklist.t
val sc : (se, SESet.t) Hashtbl.t
val reverse_sc : (se, SESet.t) Hashtbl.t
val lookup_sc : se -> SESet.t
val update_worklist : se -> SESet.t -> unit
val update_sc : se -> SESet.t -> unit
val get_context : se -> string
val init_sc : se -> se list -> unit

type var_se_tbl = (string, (CL.Ident.t, tagged_expr) Hashtbl.t) Hashtbl.t

val global_env : var_se_tbl
val unresolved_ids : (CL.Ident.t, unit) Hashtbl.t
val init_id : CL.Ident.t -> tagged_expr -> unit
val lookup_id : id -> tagged_expr
val label_to_summary : (loc, code_loc) Hashtbl.t
val list_to_array : 'a list -> 'a array

(* for resolution *)
val changed : bool ref
val exn_of_file : (string, se list) Hashtbl.t
val update_exn_of_file : string -> se list -> unit
