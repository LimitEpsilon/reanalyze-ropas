[%%import "../config.h"]

open SetExpression

let isApply : CL.Types.value_description -> bool = function
  | {val_kind = Val_prim {prim_name = "%apply"}} -> true
  | _ -> false

let isRevapply : CL.Types.value_description -> bool = function
  | {val_kind = Val_prim {prim_name = "%revapply"}} -> true
  | _ -> false

let string_of_prim : CL.Types.value_description -> string = function
  | {val_kind = Val_prim {prim_name = s1; prim_native_name = s2}} ->
    Printf.sprintf "%s->%S" s1 s2
  | _ -> ""

let print_prim v = prerr_string @@ string_of_prim v ^ "\n"

let isRaise : CL.Types.value_description -> bool = function
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

let rec resolve_path (path : CL.Path.t) =
  match path with
  | Pident x -> se_of_var x
  | ((Pdot (m, x, _)) [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    let m = resolve_path m in
    Fld (m, (Some (x, None), se_of_int 0))
  | ((Pdot (m, x)) [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    let m = resolve_path m in
    Fld (m, (Some (x, None), se_of_int 0))
  | Papply (f, x) ->
    let f = resolve_path f in
    let x = resolve_path x in
    App_V (f, [Some x])

let resolve_to_be_resolved () =
  let resolve loc path =
    try update_sc (val_of_loc loc) (resolve_path path)
    with _ ->
      if !Common.Cli.debug then (
        prerr_string "Look at : ";
        CL.Location.print_loc Format.str_formatter loc;
        prerr_string (Format.flush_str_formatter () ^ "\n"))
  in
  Hashtbl.iter resolve to_be_resolved

let exn_of_file = Hashtbl.create 10

let update_exn_of_file (key : string) (data : unit se) =
  Hashtbl.add exn_of_file key data

let connect_node_to_se loc v p =
  let value = val_of_loc loc in
  let exn = packet_of_loc loc in
  update_sc value v;
  update_sc exn p

let traverse_ast () =
  let super = CL.Tast_mapper.default in
  let expr (self : CL.Tast_mapper.mapper) (expr : CL.Typedtree.expression) =
    let v, p = se_of_expr expr in
    (* first compute v, p for the AST node *)
    connect_node_to_se expr.exp_loc v p;
    (* then update set constraints *)
    super.expr self expr (* then recurse! *)
  in
  let structure_item (self : CL.Tast_mapper.mapper)
      (struct_item : CL.Typedtree.structure_item) =
    let v, p = se_of_struct_item struct_item in
    connect_node_to_se struct_item.str_loc v p;
    super.structure_item self struct_item
  in
  let value_binding (self : CL.Tast_mapper.mapper)
      (vb : CL.Typedtree.value_binding) =
    let v, p = se_of_vb vb in
    connect_node_to_se vb.vb_loc v p;
    super.value_binding self vb
  in
  let module_binding (self : CL.Tast_mapper.mapper)
      (mb : CL.Typedtree.module_binding) =
    let v, p = se_of_mb mb in
    connect_node_to_se mb.mb_loc v p;
    super.module_binding self mb
  in
  let module_expr (self : CL.Tast_mapper.mapper) (me : CL.Typedtree.module_expr)
      =
    let v, p = se_of_module_expr me in
    connect_node_to_se me.mod_loc v p;
    super.module_expr self me
  in
  let open CL.Tast_mapper in
  {super with expr; value_binding; structure_item; module_binding; module_expr}

let process_structure (structure : CL.Typedtree.structure) =
  let traverse_ast = traverse_ast () in
  structure |> traverse_ast.structure traverse_ast |> ignore

let processCmt (cmt_infos : CL.Cmt_format.cmt_infos) =
  let id = CL.Ident.create_persistent cmt_infos.cmt_modname in
  let filename =
    match cmt_infos.cmt_sourcefile with None -> "" | Some s -> s
  in
  match cmt_infos.cmt_annots with
  | Interface _ -> ()
  | Implementation structure ->
    let v, p = se_of_struct structure in
    update_var id v;
    update_exn_of_file filename p;
    structure |> process_structure
  | _ -> ()

let reportResults ~ppf:_ =
  resolve_to_be_resolved ();
  if !Common.Cli.debug then PrintSE.print_sc_info ()
