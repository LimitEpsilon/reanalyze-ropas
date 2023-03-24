(*
 * Copyright (c) Programming Research Laboratory (ROPAS)
 *               Seoul National University, Korea
 * Copyright (c) ReScript Association
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

[%%import "../../config.h"]

open CL
open SetExpression
open GenerateConstraints
open Reduce

let traverse_ast () =
  let super = Tast_mapper.default in
  let expr (self : Tast_mapper.mapper) (expr : Typedtree.expression) =
    let v, p = se_of_expr expr in
    (* first compute v, p for the AST node *)
    init_sc (Var (val_of_expr expr)) v;
    init_sc (Var (packet_of_expr expr)) p;
    (* then update set constraints *)
    super.expr self expr (* then recurse! *)
  in
  let module_expr (self : Tast_mapper.mapper) (me : Typedtree.module_expr) =
    let v, p = se_of_module_expr me in
    init_sc (Var (val_of_mod me)) v;
    init_sc (Var (packet_of_mod me)) p;
    super.module_expr self me
  in
  let open Tast_mapper in
  {super with expr; module_expr}

let process_structure (structure : Typedtree.structure) =
  let traverse_ast = traverse_ast () in
  structure |> traverse_ast.structure traverse_ast |> ignore

let processCmt (cmt_infos : Cmt_format.cmt_infos) =
  let id = Ident.create_persistent cmt_infos.cmt_modname in
  let () = current_module := cmt_infos.cmt_modname in
  let filename =
    match cmt_infos.cmt_sourcefile with None -> "" | Some s -> s
  in
  match cmt_infos.cmt_annots with
  | Interface _ -> ()
  | Implementation structure ->
    let v, p = se_of_struct structure in
    let temp = new_temp_var () in
    init_sc (Var temp) v;
    init_id id temp;
    update_exn_of_file filename p;
    structure |> process_structure
  | _ -> ()

let print_time () =
  prerr_endline @@ "Time spent in variable propagation: "
  ^ string_of_float !time_spent_in_var;
  prerr_endline @@ "Time spent in filter_pat: "
  ^ string_of_float !time_spent_in_filter;
  prerr_endline @@ "Time spent in closure propagation: "
  ^ string_of_float !time_spent_in_closure;
  prerr_endline @@ "Time spent in constructor/record propagation: "
  ^ string_of_float !time_spent_in_fld;
  prerr_endline @@ "Time spent in update: "
  ^ string_of_float !time_spent_in_update;
  prerr_endline @@ "Time spent in constant propagation: "
  ^ string_of_float !time_spent_in_const

let reportResults ~ppf:_ =
  solve ();
  PrintSE.print_exa ();
  if !Common.Cli.debug_time then print_time ();
  if !Common.Cli.debug then PrintSE.print_sc_info ()
