(*
 * Copyright (c) Programming Research Laboratory (ROPAS)
 *               Seoul National University, Korea
 * Copyright (c) ReScript Association
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

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
  | Temp

and loc = int * string (* records the file the address belongs to *)
and tagged_expr = Val of loc | Packet of loc
and id = CL.Ident.t * string
and param = id option (* use Texp_function's param *)
and arg = tagged_expr option list

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

(** set expression type *)
and _ se =
  | Top : _ se  (** _ *)
  | Const : CL.Asttypes.constant -> _ se
  | Ctor_pat : ctor * pattern se list -> _ se  (** For pattern screening *)
  | Var : tagged_expr -> value se  (** set variable *)
  | Loc : loc -> value se  (** !ℓ *)
  | Id : id -> value se  (** identifiers *)
  | Prim : CL.Primitive.description -> value se
      (** primitives, later converted to top/fld/arr/ctor *)
  | Fn : param * loc list -> value se  (** lambda expression *)
  | App_v : tagged_expr * arg -> value se
      (** possible values / force when arg = nil *)
  | Prim_v : CL.Primitive.description * arg -> value se
  | App_p : tagged_expr * arg -> value se
      (** possible exn packets / force when arg = nil *)
  | Prim_p : CL.Primitive.description * arg -> value se
  | Ctor : ctor * (loc * pattern se option) list -> value se
      (** One ADT to rule them all :D *)
  | Arr : loc -> value se  (** Dynamically allocated arrays *)
  | Fld : tagged_expr * fld -> value se  (** field of a record / deconstruct *)
  | Diff : tagged_expr * pattern se -> value se  (** screening *)

let pat_to_val : pattern se -> value se = function
  | Top -> Top
  | Const c -> Const c
  | Ctor_pat (k, l) -> Ctor_pat (k, l)

let val_to_pat : value se -> pattern se option = function
  | (Top | Const _ | Ctor_pat _) as p -> Some p
  | _ -> None

(** For labelling expressions and memory locations *)
module LocSet = Set.Make (struct
  type t = loc

  let compare = compare
end)

let current_module = ref ""

(** Tracks the number of memory locations labelled for each file *)
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

(** Tracks the number of expressions labelled for each file *)
let expression_label : (string, int) t = create 10

let label_to_summary : (loc, code_loc) t = create 10
let summary_to_label : (code_loc, loc) t = create 10

let new_temp_var () =
  let mod_name = !current_module in
  let temp =
    match find expression_label mod_name with
    | exception Not_found ->
      add expression_label mod_name 0;
      0
    | lbl ->
      replace expression_label mod_name (lbl + 1);
      lbl + 1
  in
  let lbl = (temp, mod_name) in
  add label_to_summary lbl Temp;
  Val lbl

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

let val_of_mod me = Val (loc_of_mod me)
let packet_of_mod me = Packet (loc_of_mod me)

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

let val_of_expr e = Val (loc_of_expr e)
let packet_of_expr e = Packet (loc_of_expr e)

(** For updating set constraints *)

module SESet = Set.Make (struct
  type t = value se

  let compare = compare
end)

module Worklist = struct
  type t = SESet.t ref

  let add x (worklist : t) = worklist := SESet.add x !worklist
  let mem x (worklist : t) = SESet.mem x !worklist

  let prepare_step (worklist : t) (prev_worklist : t) =
    prev_worklist := !worklist;
    worklist := SESet.empty
end

let worklist : Worklist.t = ref SESet.empty
let prev_worklist : Worklist.t = ref SESet.empty
let sc : (value se, SESet.t) t = create 10
let reverse_sc : (value se, SESet.t) t = create 10
let changed = ref false
let lookup_sc se = try find sc se with Not_found -> SESet.empty

type var_se_tbl = (string, (CL.Ident.t, tagged_expr) t) t

let global_env : var_se_tbl = create 10
let unresolved_ids : (CL.Ident.t, unit) t = create 10

(** lookup the identifier x called from module ctx under env, raises [Not_found] when the appropriate expr is not found *)
let lookup_id (x, ctx) =
  let local_tbl = Hashtbl.find global_env ctx in
  try Hashtbl.find local_tbl x
  with Not_found -> (
    let linking_tbl = Hashtbl.find global_env (CL.Ident.name x) in
    try Hashtbl.find linking_tbl x
    with Not_found ->
      (* record unresolved identifier *)
      replace unresolved_ids x ();
      raise Not_found)

exception Escape

let to_be_filtered : Worklist.t = ref SESet.empty
let reverse_mem : (loc, SESet.t) t = create 10

let update_worklist key set =
  let summarize elt =
    let idx =
      match elt with
      | App_v (e, (Some _ :: _ | []))
      | App_p (e, (Some _ :: _ | []))
      | Fld (e, _) ->
        Worklist.add (Var e) worklist;
        Var e
      | Diff (e, _) ->
        Worklist.add (Var e) worklist;
        Worklist.add (Var e) to_be_filtered;
        Var e
      | Var _ | Loc _ | Id _ ->
        Worklist.add elt worklist;
        elt
      | Ctor (_, l) ->
        if Worklist.mem key to_be_filtered then
          List.iter
            (fun (l, _) ->
              match find reverse_mem l with
              | exception Not_found -> add reverse_mem l (SESet.singleton key)
              | original -> replace reverse_mem l (SESet.add key original))
            l;
        raise Escape
      | _ -> raise Escape
    in
    match find reverse_sc idx with
    | exception Not_found -> add reverse_sc idx (SESet.singleton key)
    | orig -> replace reverse_sc idx (SESet.add key orig)
  in
  match key with
  | Fld (e, _) -> summarize (Var e)
  | Loc l ->
    let reverse_set = try find reverse_mem l with Not_found -> SESet.empty in
    SESet.iter (fun x -> Worklist.add x worklist) reverse_set;
    Worklist.add key worklist;
    SESet.iter (fun se -> try summarize se with Escape -> ()) set
  | Var _ ->
    Worklist.add key worklist;
    SESet.iter (fun se -> try summarize se with Escape -> ()) set
  | _ -> failwith "Invalid LHS"

let update_sc lhs added =
  let true_if_val x =
    match val_to_pat x with Some _ -> true | None -> false
  in
  let original = lookup_sc lhs in
  let added_val, added_pat = SESet.partition true_if_val added in
  let diff_val = SESet.diff added_val original in
  let diff_pat =
    if SESet.mem Top original then SESet.empty
    else if SESet.mem Top added_pat then SESet.singleton Top
    else SESet.diff added_pat original
  in
  let diff = SESet.union diff_val diff_pat in
  if not (SESet.is_empty diff) then (
    changed := true;
    update_worklist lhs diff;
    replace sc lhs (SESet.union original diff))

let get_context = function
  | Fld ((Packet (_, ctx) | Val (_, ctx)), _)
  | Var (Packet (_, ctx) | Val (_, ctx))
  | Loc (_, ctx) ->
    ctx
  | _ -> failwith "Not a valid LHS"

(* enforce data to be nonempty *)
let init_sc lhs data =
  if data = [] then ()
  else
    let set = SESet.of_list data in
    update_worklist lhs set;
    match find sc lhs with
    | exception Not_found -> add sc lhs set
    | original -> replace sc lhs (SESet.union original set)

let init_id id expr =
  match find global_env !current_module with
  | exception Not_found ->
    let tbl = create 10 in
    add tbl id expr;
    add global_env !current_module tbl
  | tbl -> replace tbl id expr

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

(* for resolution *)
let rec val_of_path = function
  | CL.Path.Papply (f, x) ->
    let f = val_of_path f in
    let x = val_of_path x in
    let temp = new_temp_var () in
    init_sc (Var temp) [App_v (f, [Some x])];
    temp
  | ((CL.Path.Pdot (x, fld, _)) [@if ocaml_version < (4, 08, 0) || defined npm])
    ->
    let x = val_of_path x in
    let temp = new_temp_var () in
    init_sc (Var temp) [Fld (x, (Some fld, Some 0))];
    temp
  | ((CL.Path.Pdot (x, fld))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let x = val_of_path x in
    let temp = new_temp_var () in
    init_sc (Var temp) [Fld (x, (Some fld, Some 0))];
    temp
  | CL.Path.Pident x ->
    let temp = new_temp_var () in
    init_sc (Var temp) [Id (x, !current_module)];
    temp

let exn_of_file = create 10

let update_exn_of_file (key : string) (data : value se list) =
  add exn_of_file key data

(* let inline_table : (id, SESet.t) Hashtbl.t = create 10 *)
(* let address_translations : (loc, loc) Hashtbl.t = create 10 *)
(* let expr_translations : (loc, loc) Hashtbl.t = create 10 *)

(* let need_to_inline x m = *)
(*   match find inline_table x with *)
(*   | exception Not_found -> None *)
(*   | s -> *)
(*     if SESet.mem m s then Some false *)
(*     else ( *)
(*       replace inline_table x (SESet.add m s); *)
(*       clear inline_translations; *)
(*       Some true) *)

(* let rec translate x m is_var (lbl, ctx) = *)
(*   match find inline_translations (lbl, ctx) with *)
(*   | exception Not_found -> *)
(*     let inlined = if is_var then 1 else 2 in *)
(*     let inlined = (inlined, ctx) in *)
(*     add inline_translations (lbl, ctx) inlined; *)
(*     inlined *)
(*   | se -> se *)
