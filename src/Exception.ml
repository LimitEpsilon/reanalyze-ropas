[%%import "../config.h"]

open CL
open SetExpression
open GenerateConstraints
open Reduce

let rec resolve_path (path : Path.t) (context : string) =
  match path with
  | Pident x -> se_of_var x context
  | ((Pdot (m, x, _)) [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let m_temp = Var (Val (new_temp_var context)) in
    let m = resolve_path m context in
    update_sc m_temp m;
    [Fld (m_temp, (Some x, Some 0))]
  | ((Pdot (m, x)) [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let m_temp = Var (Val (new_temp_var context)) in
    let m = resolve_path m context in
    update_sc m_temp m;
    [Fld (m_temp, (Some x, Some 0))]
  | Papply (f, x) ->
    let f_temp = Var (Val (new_temp_var context)) in
    let x_temp = Var (Val (new_temp_var context)) in
    let f = resolve_path f context in
    let x = resolve_path x context in
    update_sc f_temp f;
    update_sc x_temp x;
    [App_V (f_temp, [Some x_temp])]

let resolve_to_be_resolved () =
  let resolve loc (path, context) =
    let var = Var (Val (Expr loc)) in
    try
      update_sc var (resolve_path path context);
      Efficient_hashtbl.remove to_be_resolved loc
    with _ ->
      if !Common.Cli.debug then (
        let loc =
          match Efficient_hashtbl.find label_to_summary loc with
          | Expr_loc e -> e.exp_loc
          | Mod_loc m -> m.mod_loc
          | Bop_loc t -> t.val_loc
        in
        prerr_string "Look at : ";
        Location.print_loc Format.str_formatter loc;
        prerr_string (Format.flush_str_formatter () ^ "\n"))
  in
  Efficient_hashtbl.iter resolve to_be_resolved

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
  let () = current_module := cmt_infos.cmt_modname in
  let filename =
    match cmt_infos.cmt_sourcefile with None -> "" | Some s -> s
  in
  let () =
    match cmt_infos.cmt_annots with
    | Interface _ -> ()
    | Implementation structure ->
      let v, p = se_of_struct structure in
      update_var id v;
      update_exn_of_file filename p;
      structure |> process_structure
    | _ -> ()
  in
  linking := false;
  resolve_to_be_resolved ();
  solve !current_module;
  ()

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
  linking := true;
  resolve_to_be_resolved () (* linking *);
  solve "" (* linking *);
  if !Common.Cli.closure then PrintSE.print_closure () else PrintSE.print_exa ();
  if !Common.Cli.debug_time then print_time () else ();
  if !Common.Cli.debug then PrintSE.print_grammar ()
