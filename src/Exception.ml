[%%import "../config.h"]

open CL
open SetExpression
open Reduce

let isApply : Types.value_description -> bool = function
  | {val_kind = Val_prim {prim_name = "%apply"}} -> true
  | _ -> false

let isRevapply : Types.value_description -> bool = function
  | {val_kind = Val_prim {prim_name = "%revapply"}} -> true
  | _ -> false

let string_of_prim : Types.value_description -> string = function
  | {val_kind = Val_prim {prim_name = s1; prim_native_name = s2}} ->
    Printf.sprintf "%s->%S" s1 s2
  | _ -> ""

let print_prim v = prerr_string @@ string_of_prim v ^ "\n"

let isRaise : Types.value_description -> bool = function
  | {
      val_kind =
        Val_prim
          {
            prim_name =
              "%raise" | "%raise_notrace" | "%reraise" | "%raise_with_backtrace";
          };
    } ->
    true (* do not consider second argument for raise_with_backtrace *)
  | _ -> false

let rec resolve_path (path : Path.t) =
  match path with
  | Pident x -> se_of_var x
  | ((Pdot (m, x, _)) [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let m_temp = Var (Val (new_temp_var ())) in
    let m = resolve_path m in
    update_sc m_temp m;
    [Fld (m_temp, (Some x, Some 0))]
  | ((Pdot (m, x)) [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let m_temp = Var (Val (new_temp_var ())) in
    let m = resolve_path m in
    update_sc m_temp m;
    [Fld (m_temp, (Some x, Some 0))]
  | Papply (f, x) ->
    let f_temp = Var (Val (new_temp_var ())) in
    let x_temp = Var (Val (new_temp_var ())) in
    let f = resolve_path f in
    let x = resolve_path x in
    update_sc f_temp f;
    update_sc x_temp x;
    [App_V (f_temp, [Some x_temp])]

let resolve_to_be_resolved () =
  let resolve loc path =
    try update_sc (Var (Val (Expr loc))) (resolve_path path)
    with _ ->
      if !Common.Cli.debug then (
        let loc =
          match loc with
          | Expr_loc e -> e.exp_loc
          | Mod_loc m -> m.mod_loc
          | Bop_loc t -> t.val_loc
        in
        prerr_string "Look at : ";
        Location.print_loc Format.str_formatter loc;
        prerr_string (Format.flush_str_formatter () ^ "\n"))
  in
  Hashtbl.iter resolve to_be_resolved

let traverse_ast () =
  let super = Tast_mapper.default in
  let expr (self : Tast_mapper.mapper) (expr : Typedtree.expression) =
    let v, p = se_of_expr expr in
    (* first compute v, p for the AST node *)
    update_sc (val_of_expr expr) v;
    update_sc (packet_of_expr expr) p;
    (* then update set constraints *)
    super.expr self expr (* then recurse! *)
  in
  let module_expr (self : Tast_mapper.mapper) (me : Typedtree.module_expr) =
    let v, p = se_of_module_expr me in
    update_sc (val_of_mod me) v;
    update_sc (packet_of_mod me) p;
    super.module_expr self me
  in
  let open Tast_mapper in
  {super with expr; module_expr}

let process_structure (structure : Typedtree.structure) =
  let traverse_ast = traverse_ast () in
  structure |> traverse_ast.structure traverse_ast |> ignore

let processCmt (cmt_infos : Cmt_format.cmt_infos) =
  let id = Ident.create_persistent cmt_infos.cmt_modname in
  let filename =
    match cmt_infos.cmt_sourcefile with None -> "" | Some s -> s
  in
  match cmt_infos.cmt_annots with
  | Interface _ -> ()
  | Implementation structure ->
    let v, p = se_of_struct structure in
    current_file := (Hashtbl.create 10);
    update_var id v;
    update_exn_of_file filename p;
    structure |> process_structure
  | _ -> ()

let reportResults ~ppf:_ =
  resolve_to_be_resolved ();
  solve ();
  if !Common.Cli.closure then PrintSE.print_closure ()
  else PrintSE.print_exa ();
  if !Common.Cli.debug then PrintSE.print_grammar ()
