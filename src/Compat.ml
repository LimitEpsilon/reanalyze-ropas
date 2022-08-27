[%%import "../config.h"]

open CL

[%%if ocaml_version >= (4, 08, 0) && not_defined npm]

let getStringTag s = match s with Format.String_tag s -> s | _ -> ""

[%%else]

let getStringTag s = s

[%%endif]
[%%if ocaml_version >= (4, 08, 0) && not_defined npm]

let filter_map = List.filter_map

[%%else]

(* https://github.com/ocaml/ocaml/blob/9a31c888b177f3aa603bbbe17852cbb57f047df4/stdlib/list.ml#L254-L262 passed though refmt *)
let filter_map f =
  let rec aux accu = function
    | [] -> List.rev accu
    | x :: l -> (
      match f x with None -> aux accu l | Some v -> aux (v :: accu) l)
  in
  aux []

[%%endif]

let getStringValue const =
  match const with
  | ((Parsetree.Pconst_string (s, _, _))
  [@if ocaml_version >= (4, 11, 0) && not_defined npm]) ->
    s
  | ((Parsetree.Pconst_string (s, _))
  [@if ocaml_version < (4, 11, 0) || defined npm]) ->
    s
  | _ -> assert false

let getConstString const =
  match const with
  | ((Asttypes.Const_string (s, _, _))
  [@if ocaml_version >= (4, 11, 0) && not_defined npm]) ->
    s
  | ((Asttypes.Const_string (s, _))
  [@if ocaml_version < (4, 11, 0) || defined npm]) ->
    s
  | _ -> assert false

[%%if ocaml_version >= (4, 11, 0) && not_defined npm]

type 'a typedtreeCase = 'a Typedtree.case

[%%else]

type 'a typedtreeCase = Typedtree.case

[%%endif]
[%%if ocaml_version >= (4, 11, 0) && not_defined npm]

type 'a generalPattern = 'a Typedtree.general_pattern

[%%else]

type 'a generalPattern = Typedtree.pattern

[%%endif]
[%%if ocaml_version >= (4, 13, 0) && not_defined npm]

type ('a, 'b) type_kind = ('a, 'b) Types.type_kind

[%%else]

type ('a, 'b) type_kind = Types.type_kind

[%%endif]
[%%if ocaml_version >= (4, 11, 0) && not_defined npm]

let unboxPatCstrName pat =
  match pat.Typedtree.pat_desc with
  | Typedtree.Tpat_value v -> (
    match
      (v :> Typedtree.value Typedtree.pattern_desc Typedtree.pattern_data)
        .pat_desc
    with
    | ((Tpat_construct (_, {cstr_name}, _, _))
    [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
      Some cstr_name
    | ((Tpat_construct (_, {cstr_name}, _))
    [@if ocaml_version < (4, 13, 0) || defined npm]) ->
      Some cstr_name
    | _ -> None)
  | _ -> None

[%%else]

let unboxPatCstrName pat =
  match pat.Typedtree.pat_desc with
  | Tpat_construct (_, {cstr_name}, _) -> Some cstr_name
  | _ -> None

[%%endif]

let unboxPatCstrTxt pat =
  match pat with
  | ((Typedtree.Tpat_construct ({txt}, _, _, _))
  [@if ocaml_version >= (4, 13, 0) && not_defined npm]) ->
    txt
  | ((Typedtree.Tpat_construct ({txt}, _, _))
  [@if ocaml_version < (4, 13, 0) || defined npm]) ->
    txt
  | _ -> assert false

[%%if ocaml_version >= (4, 08, 0) && not_defined npm]

let setOpenCloseTag openTag closeTag =
  {
    Format.mark_open_stag = openTag;
    mark_close_stag = closeTag;
    print_open_stag = (fun _ -> ());
    print_close_stag = (fun _ -> ());
  }

[%%else]

let setOpenCloseTag openTag closeTag =
  {
    Format.mark_open_tag = openTag;
    mark_close_tag = closeTag;
    print_open_tag = (fun _ -> ());
    print_close_tag = (fun _ -> ());
  }

[%%endif]
[%%if ocaml_version >= (4, 08, 0) && not_defined npm]

let pp_set_formatter_tag_functions = Format.pp_set_formatter_stag_functions

[%%else]

let pp_set_formatter_tag_functions =
  (Format.pp_set_formatter_tag_functions [@warning "-3"])

[%%endif]

let getSigValue si =
  match si with
  | ((Types.Sig_value (id, {Types.val_loc; val_kind; val_type}, _))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    (id, val_loc, val_kind, val_type)
  | ((Types.Sig_value (id, {Types.val_loc; val_kind; val_type}))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    (id, val_loc, val_kind, val_type)
  | _ -> assert false

let getSigType si =
  match si with
  | ((Types.Sig_type (id, t, _, _))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    (id, t)
  | ((Types.Sig_type (id, t, _))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    (id, t)
  | _ -> assert false

let getTSubst td =
  match td with
  | ((Types.Tsubst (t, _)) [@if ocaml_version >= (4, 13, 0) && not_defined npm])
    ->
    t
  | ((Types.Tsubst t) [@if ocaml_version < (4, 13, 0) || defined npm]) -> t
  | _ -> assert false

let getTypeVariant (tk : ('a, 'b) type_kind) =
  match tk with
  | ((Type_variant (l, _)) [@if ocaml_version >= (4, 13, 0) && not_defined npm])
    ->
    l
  | ((Type_variant l) [@if ocaml_version < (4, 13, 0) || defined npm]) -> l
  | _ -> assert false

let getSigModuleModtype si =
  match si with
  | ((Types.Sig_module
       (id, _, {Types.md_type = moduleType; md_loc = loc}, _, _))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    Some (id, moduleType, loc)
  | ((Types.Sig_modtype
       (id, {Types.mtd_type = Some moduleType; mtd_loc = loc}, _))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    Some (id, moduleType, loc)
  | ((Types.Sig_module (id, {Types.md_type = moduleType; md_loc = loc}, _))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    Some (id, moduleType, loc)
  | ((Types.Sig_modtype (id, {Types.mtd_type = Some moduleType; mtd_loc = loc}))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    Some (id, moduleType, loc)
  | _ -> None

let getMtyFunctorModuleType (moduleType : Types.module_type) =
  match moduleType with
  | ((Mty_functor (Named (_, mtParam), mt))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    Some (Some mtParam, mt)
  | ((Mty_functor (Unit, mt))
  [@if ocaml_version >= (4, 10, 0) && not_defined npm]) ->
    Some (None, mt)
  | ((Mty_functor (_, mtParam, mt))
  [@if ocaml_version < (4, 10, 0) || defined npm]) ->
    Some (mtParam, mt)
  | _ -> None

let getTexpMatch desc =
  match desc with
  | ((Typedtree.Texp_match (e, cases, partial))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    (e, cases, partial)
  | ((Typedtree.Texp_match (e, casesOK, casesExn, partial))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    (e, casesOK @ casesExn, partial)
  | _ -> assert false

let texpMatchGetExceptions desc =
  match desc with
  | ((Typedtree.Texp_match (_, cases, _))
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    cases
    |> List.filter_map (fun {Typedtree.c_lhs = pat} ->
           match pat.pat_desc with
           | Tpat_exception {pat_desc} -> Some pat_desc
           | _ -> None)
  | ((Typedtree.Texp_match (_, _, casesExn, _))
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    casesExn |> List.map (fun (case : Typedtree.case) -> case.c_lhs.pat_desc)
  | _ -> assert false

let texpMatchHasExceptions desc = texpMatchGetExceptions desc != []

[%%if ocaml_version >= (4, 08, 0) && not_defined npm]

let getPayload x =
  let {Parsetree.attr_name = {txt}; attr_payload = payload} = x in
  (txt, payload)

[%%else]

let getPayload x = let {Asttypes.txt}, payload = x in

                   (txt, payload)

[%%endif]
[%%if ocaml_version >= (4, 08, 0) && not_defined npm]

module Ident = struct
  include Ident

  let create = Ident.create_local
end

[%%else]

module Ident = struct
  include Ident
end

[%%endif]

let tstrExceptionGet (x : Typedtree.structure_item_desc) =
  match x with
  | ((Tstr_exception {tyexn_constructor = {ext_id}; tyexn_loc})
  [@if ocaml_version >= (4, 08, 0) && not_defined npm]) ->
    Some (ext_id, tyexn_loc)
  | ((Tstr_exception {ext_id; ext_loc})
  [@if ocaml_version < (4, 08, 0) || defined npm]) ->
    Some (ext_id, ext_loc)
  | _ -> None

[%%if ocaml_version >= (4, 10, 0) && not_defined npm]

let moduleIdName nameOpt =
  match nameOpt with None -> "UnnamedModule" | Some name -> name |> Ident.name

[%%else]

let moduleIdName name = name |> Ident.name

[%%endif]
[%%if ocaml_version >= (4, 14, 0) && not_defined npm]

let get_desc = Types.get_desc

[%%else]

let get_desc x = x.Types.desc

[%%endif]
