[%%import "../../config.h"]

open Hashtbl

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

and param = (CL.Ident.t * string) option (* use Texp_function's param *)
and arg = value se option list

and _ expr =
  | Expr_var : (CL.Ident.t * string) -> param expr (* record the file *)
  | Expr : loc -> loc expr

and arr =
  | Static of loc list
      (** statically allocated arrays such as records, variants, or tuples *)
  | Dynamic of loc
      (** dynamically allocated array, decoded from the Prim set expression *)

and _ tagged_expr =
  | Val : 'a expr -> 'a tagged_expr
  | Packet : 'a expr -> 'a tagged_expr

and ctor = string option
(** variant : Some Types.cstr_name
    polymorphic variant : Some Asttypes.label
    tuple or record or array : None *)

and fld = ctor * int option
(** i-th field of a variant : (Some κ, Some i)
    i-th field of a tuple or record : (None, Some i)
    dynamic access through the Array.get primitive : (None, None) *)

and pattern
(* phantom type for pattern screening *)

and value
and loc = int * string (* records the file the address belongs to *)

(** set expression type *)
and _ se =
  | Top : _ se  (** _ *)
  | Const : CL.Asttypes.constant -> _ se
  | Const_top : pattern se
  | Prim : CL.Primitive.description -> value se
      (** primitives, later converted to arith/rel/fld/mem *)
  | Fn : param * loc expr list -> value se  (** lambda expression *)
  | Var : _ tagged_expr -> _ se  (** set variable *)
  | App_V : value se * arg -> value se
      (** possible values / force when arg = nil / prim_v when lhs is Prim *)
  | App_P : value se * arg -> value se
      (** possible exn packets / force when arg = nil / prim_p when lhs is Prim *)
  | Ctor : ctor * arr -> value se  (** One ADT to rule them all :D *)
  | Ctor_pat : ctor * pattern se list -> pattern se
      (** For pattern screening *)
  | Arr_pat : loc -> pattern se
  | Fld : value se * fld -> value se  (** field of a record / deconstruct *)
  | Diff : value se * pattern se -> value se  (** screening *)
  | Loc : loc * pattern se option -> pattern se

(* divide_by_zero : check denominator, if constant check if zero.
                  : if identifier look up in var_to_se to check if constant
                  : if constant check if zero, else mark might_raise *)
module Loc = struct
  type t = loc

  let compare = compare
end

module LocSet = Set.Make (Loc)

let current_module = ref ""
let temp_variable_label : (string, int) t = create 10

let new_temp_var mod_name =
  let temp =
    match find temp_variable_label mod_name with
    | exception Not_found ->
      add temp_variable_label mod_name 0;
      0
    | lbl ->
      replace temp_variable_label mod_name (lbl + 1);
      lbl + 1
  in
  let temp_id =
    CL.Ident.create_persistent (mod_name ^ "__temp" ^ string_of_int temp)
  in
  Expr_var (temp_id, mod_name)

let address : (string, int) t = create 10

let new_memory mod_name =
  let mem =
    match find address mod_name with
    | exception Not_found ->
      add address mod_name 0;
      0
    | addr ->
      replace address mod_name (addr + 1);
      addr + 1
  in
  (mem, mod_name)

let new_array size =
  let arr = Array.make size !current_module in
  Array.map new_memory arr

module SE = struct
  type t = value se

  let compare = compare
end

module SESet = struct
  module Internal = Set.Make (SE)

  type t = Set of Internal.t | Total

  let empty = Set Internal.empty

  let mem (x : value se) (set : t) =
    match set with Total -> true | Set s -> Internal.mem x s

  let add (x : value se) (set : t) =
    match (x, set) with
    | Top, _ -> Total
    | _, Total -> Total
    | _, Set s -> Set (Internal.add x s)

  let inter (s1 : t) (s2 : t) =
    match (s1, s2) with
    | _, Total -> s1
    | Total, _ -> s2
    | Set s1, Set s2 -> Set (Internal.inter s1 s2)

  let union (s1 : t) (s2 : t) =
    match (s1, s2) with
    | _, Total -> Total
    | Total, _ -> Total
    | Set s1, Set s2 -> Set (Internal.union s1 s2)

  let diff (s1 : t) (s2 : t) =
    match (s1, s2) with
    | _, Total -> Set Internal.empty
    | Total, _ -> Total
    | Set s1, Set s2 -> Set (Internal.diff s1 s2)

  let is_empty = function Total -> false | Set s -> Internal.is_empty s
  let elements = function Total -> [Top] | Set s -> Internal.elements s
  let of_list l = if List.mem Top l then Total else Set (Internal.of_list l)

  let filter f = function
    | Total -> if f Top then Total else empty
    | Set s -> Set (Internal.filter f s)

  let iter f = function Total -> f Top | Set s -> Internal.iter f s

  let fold f set acc =
    match set with Total -> f Top acc | Set s -> Internal.fold f s acc

  let singleton = function Top -> Total | x -> Set (Internal.singleton x)

  let map f = function
    | Total ->
      let elt = f Top in
      singleton elt
    | Set s ->
      let set = Internal.map f s in
      if Internal.mem Top set then Total else Set set
end

module Worklist = struct
  type t = (int, unit) Hashtbl.t

  let add x (worklist : t) = if mem worklist x then () else add worklist x ()
  let mem x (worklist : t) = mem worklist x

  let prepare_step (worklist : t) (prev_worklist : t) =
    reset prev_worklist;
    iter (fun x () -> add x prev_worklist) worklist;
    reset worklist
end

let linking = ref false
let worklist : Worklist.t = create 10
let affected_vars : (loc, Worklist.t) t = create 10
let sc : (string, (value se, SESet.t) t) t = create 10
let reverse_sc : (int, SESet.t) t = create 10
let hash = hash

let update_worklist set =
  let summarize = function
    | App_V (x, _) | App_P (x, _) -> Worklist.add (hash x) worklist
    | Var x -> Worklist.add (hash (Var x)) worklist
    | Ctor (kappa, arr) -> Worklist.add (hash (Ctor (kappa, arr))) worklist
    | _ -> ()
  in
  SESet.iter summarize set

exception Escape

let update_reverse_sc key set =
  let summarize elt =
    let idx =
      match elt with
      | App_V (x, _) | App_P (x, _) | Fld (x, _) | Diff (x, _) -> hash x
      | Var _ | Ctor _ -> hash elt
      | _ -> raise Escape
    in
    match find reverse_sc idx with
    | exception Not_found -> add reverse_sc idx (SESet.singleton key)
    | orig -> replace reverse_sc idx (SESet.add key orig)
  in
  SESet.iter (fun elt -> try summarize elt with Escape -> ()) set;
  match key with Fld (Var x, _) -> summarize (Var x) | _ -> ()

let get_context_fld = function
  | Fld
      ( Var
          ( Val (Expr (_, ctx) | Expr_var (_, ctx))
          | Packet (Expr (_, ctx) | Expr_var (_, ctx)) ),
        _ ) ->
    ctx
  | _ -> raise Not_found

let get_context = function
  | Var
      ( Val (Expr (_, ctx) | Expr_var (_, ctx))
      | Packet (Expr (_, ctx) | Expr_var (_, ctx)) ) ->
    ctx
  | _ -> raise Not_found

let lookup_sc key =
  let context = try get_context key with _ -> get_context_fld key in
  find (find sc context) key

let update_sc key data =
  let context = try get_context key with _ -> get_context_fld key in
  let sc =
    match find sc context with
    | exception Not_found ->
      let tbl = create 10 in
      add sc !current_module tbl;
      tbl
    | tbl -> tbl
  in
  let set = SESet.of_list data in
  update_worklist set;
  update_reverse_sc key set;
  if mem sc key then
    let original = find sc key in
    replace sc key (SESet.union original set)
  else (
    add sc key set;
    update_worklist (SESet.singleton key))

type var_se_tbl = (string, (CL.Ident.t, SESet.t) t) t

let var_to_se : var_se_tbl = create 10

let update_var key data =
  let set = SESet.of_list data in
  match find var_to_se !current_module with
  | exception Not_found ->
    let tbl = create 10 in
    add tbl key set;
    add var_to_se !current_module tbl
  | tbl -> (
    match find tbl key with
    | exception Not_found -> add tbl key set
    | original -> replace tbl key (SESet.union original set))

type to_be_resolved = (loc, CL.Path.t * string) t

let to_be_resolved : to_be_resolved = create 256
let update_to_be key data = add to_be_resolved key (data, !current_module)
let memory : (string, (loc, SESet.t) t) t = create 10
let reverse_mem : (int, LocSet.t) t = create 10

let update_reverse_mem key set =
  let summarize elt =
    let idx =
      match elt with
      | App_V (x, _) | App_P (x, _) | Fld (x, _) | Diff (x, _) -> hash x
      | Var _ | Ctor _ -> hash elt
      | _ -> raise Escape
    in
    match find reverse_mem idx with
    | exception Not_found -> add reverse_mem idx (LocSet.singleton key)
    | orig -> replace reverse_mem idx (LocSet.add key orig)
  in
  SESet.iter (fun elt -> try summarize elt with Escape -> ()) set

let lookup_mem key =
  let _, context = key in
  find (find memory context) key

let update_mem key data =
  let _, context = key in
  let memory =
    match find memory context with
    | exception Not_found ->
      let tbl = create 10 in
      add memory !current_module tbl;
      tbl
    | tbl -> tbl
  in
  let set = SESet.of_list data in
  update_reverse_mem key set;
  if mem memory key then
    let original = find memory key in
    replace memory key (SESet.union original set)
  else add memory key set

let list_to_array l =
  let len = List.length l in
  if len = 0 then [||]
  else
    let arr = Array.make len (List.hd l) in
    let i = ref 0 in
    let l = ref l in
    while !l <> [] do
      match !l with
      | hd :: tl ->
        arr.(!i) <- hd;
        incr i;
        l := tl
      | _ -> assert false
    done;
    arr

let se_of_var x context =
  let local_tbl = find var_to_se context in
  try SESet.elements (find local_tbl x)
  with Not_found ->
    if !linking then (
      try
        let global_tbl = find var_to_se (CL.Ident.name x) in
        SESet.elements (find global_tbl x)
      with Not_found ->
        if !Common.Cli.debug then
          prerr_string
            ("Hey, I can't figure out : " ^ CL.Ident.unique_name x ^ "\n");
        raise Not_found)
    else raise Not_found

let expression_label : (string, int) t = create 10
let label_to_summary : (loc, code_loc) t = create 10
let summary_to_label : (code_loc, loc) t = create 10

let loc_of_summary summary =
  match find summary_to_label summary with
  | exception Not_found ->
    let loc_label =
      match find expression_label !current_module with
      | exception Not_found ->
        add expression_label !current_module 0;
        0
      | i ->
        replace expression_label !current_module (i + 1);
        i + 1
    in
    let lbl = (loc_label, !current_module) in
    add label_to_summary lbl summary;
    add summary_to_label summary lbl;
    lbl
  | lbl -> lbl

let loc_of_mod mod_expr =
  let summary =
    Mod_loc
      {
        mod_type = mod_expr.CL.Typedtree.mod_type;
        mod_loc = mod_expr.CL.Typedtree.mod_loc;
        mod_context = !current_module;
      }
  in
  loc_of_summary summary

let expr_of_mod me = Expr (loc_of_mod me)
let val_of_mod me = Var (Val (expr_of_mod me))
let packet_of_mod me = Var (Packet (expr_of_mod me))

let loc_of_expr expr =
  let summary =
    Expr_loc
      {
        exp_type = expr.CL.Typedtree.exp_type;
        exp_loc = expr.CL.Typedtree.exp_loc;
        exp_context = !current_module;
      }
  in
  loc_of_summary summary

let expr_of_expr e = Expr (loc_of_expr e)
let val_of_expr e = Var (Val (expr_of_expr e))
let packet_of_expr e = Var (Packet (expr_of_expr e))

(* for resolution *)
let changed = ref false
let prev_worklist : Worklist.t = create 10
let exn_of_file = create 10

module GE = struct
  type t = pattern se

  let compare = compare
end

module GESet = struct
  module Internal = Set.Make (GE)

  type t = Set of Internal.t | Total

  let empty = Set Internal.empty

  let mem (x : pattern se) (set : t) =
    match set with Total -> true | Set s -> Internal.mem x s

  let add (x : pattern se) (set : t) =
    match (x, set) with
    | Top, _ -> Total
    | _, Total -> Total
    | _, Set s -> Set (Internal.add x s)

  let inter (s1 : t) (s2 : t) =
    match (s1, s2) with
    | _, Total -> s1
    | Total, _ -> s2
    | Set s1, Set s2 -> Set (Internal.inter s1 s2)

  let union (s1 : t) (s2 : t) =
    match (s1, s2) with
    | _, Total -> Total
    | Total, _ -> Total
    | Set s1, Set s2 -> Set (Internal.union s1 s2)

  let diff (s1 : t) (s2 : t) =
    match (s1, s2) with
    | _, Total -> Set Internal.empty
    | Total, _ -> Total
    | Set s1, Set s2 -> Set (Internal.diff s1 s2)

  let is_empty = function Total -> false | Set s -> Internal.is_empty s
  let elements = function Total -> [Top] | Set s -> Internal.elements s
  let of_list l = if List.mem Top l then Total else Set (Internal.of_list l)

  let filter f = function
    | Total -> if f Top then Total else empty
    | Set s -> Set (Internal.filter f s)

  let iter f = function Total -> f Top | Set s -> Internal.iter f s

  let fold f set acc =
    match set with Total -> f Top acc | Set s -> Internal.fold f s acc

  let singleton = function Top -> Total | x -> Set (Internal.singleton x)

  let map f = function
    | Total ->
      let elt = f Top in
      singleton elt
    | Set s ->
      let set = Internal.map f s in
      if Internal.mem Top set then Total else Set set
end

let update_l l idx =
  match find affected_vars l with
  | exception Not_found ->
    let new_tbl = create 1 in
    add new_tbl idx ();
    add affected_vars l new_tbl
  | original -> Worklist.add idx original

let update_worklist_g key set =
  let for_each_loc = function
    | Loc (l, None) -> update_l l (hash key)
    | _ -> ()
  in
  let summarize = function
    | Ctor_pat (_, arr) -> List.iter for_each_loc arr
    | Arr_pat l -> update_l l (hash key)
    | _ -> ()
  in
  GESet.iter summarize set;
  Worklist.add (hash key) worklist

let update_exn_of_file (key : string) (data : value se list) =
  add exn_of_file key data

let update_c key set =
  let context = try get_context key with _ -> get_context_fld key in
  let sc = find sc context in
  if mem sc key then
    let original = find sc key in
    let diff = SESet.diff set original in
    if SESet.is_empty diff then false
    else (
      replace sc key (SESet.union original diff);
      update_worklist (SESet.singleton key);
      update_worklist diff;
      update_reverse_sc key diff;
      changed := true;
      true)
  else (
    add sc key set;
    update_worklist (SESet.singleton key);
    update_worklist set;
    update_reverse_sc key set;
    changed := true;
    true)

let consult_affected_vars key =
  match find affected_vars key with
  | exception Not_found -> ()
  | affected -> iter (fun x () -> Worklist.add x worklist) affected

let update_loc key set =
  let _, context = key in
  let memory = find memory context in
  if mem memory key then
    let original = find memory key in
    let diff = SESet.diff set original in
    if SESet.is_empty diff then false
    else (
      replace memory key (SESet.union original diff);
      update_worklist diff;
      consult_affected_vars key;
      update_reverse_mem key diff;
      changed := true;
      true)
  else (
    add memory key set;
    update_worklist set;
    consult_affected_vars key;
    update_reverse_mem key set;
    changed := true;
    true)

let grammar : (pattern se, GESet.t) t = create 256

let update_g var set =
  let key = Var var in
  if mem grammar key then
    let original = find grammar key in
    let diff = GESet.diff set original in
    if GESet.is_empty diff then false
    else (
      replace grammar key (GESet.union original diff);
      update_worklist_g key diff;
      changed := true;
      true)
  else (
    add grammar key set;
    update_worklist_g key set;
    changed := true;
    true)

let abs_mem : (loc, GESet.t) t = create 256

let update_abs_loc key set =
  if mem abs_mem key then
    let original = find abs_mem key in
    let diff = GESet.diff set original in
    if GESet.is_empty diff then false
    else (
      replace abs_mem key (GESet.union original diff);
      consult_affected_vars key;
      changed := true;
      true)
  else (
    add abs_mem key set;
    consult_affected_vars key;
    changed := true;
    true)
