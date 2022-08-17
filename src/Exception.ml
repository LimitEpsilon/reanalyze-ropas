type param = CL.Typedtree.pattern list
and arg = code_loc expr option list
and code_loc = CL.Location.t

and _ expr =
  | Expr_var : param -> param expr
  | Expr : code_loc -> code_loc expr
  | Extern :
      string * CL.Types.type_desc
      -> code_loc expr (* blackbox, includes I/O *)

and _ tagged_expr =
  | Val : 'a expr -> 'a tagged_expr
  | Packet : 'a expr -> 'a tagged_expr

and env = Env_var | Env of (param * code_loc tagged_expr) list

(* construct : name |> string_of_longident *)
(* variant : CL.Asttypes.label *)
and ctor = string option

(* construct : need to know arity *)
(* record : translate field name to position(int, starts from 0) *)
and 'a fld = ctor * 'a se

(* CL.Types.value_description.value_kind | Val_prim of {prim_name : string ;} *)
and arithop =
  [ `ADD
  | `SUB
  | `DIV
  | `MUL
  | `NEG
  | `ABS (* absolute value *)
  | `MOD
  | `AND
  | `OR
  | `NOT
  | `XOR
  | `LSL (* <<, logical *)
  | `LSR (* >>, logical *)
  | `ASR (* >>, arithmetic sign extension *)
  | `SUCC (* ++x *)
  | `PRED (* --x *) ]

and relop =
  [ `EQ (* == *)
  | `NE (* != *)
  | `LT (* < *)
  | `LE (* <= *)
  | `GT (* > *)
  | `GE (* >= *) ]

(* set expression type *)
and _ se =
  | Bot : _ se (* empty set *)
  | Top : _ se (* _ *)
  | Const : CL.Asttypes.constant -> _ se
  | Fn : param * code_loc expr list -> unit se (* context-insensitive *)
  | Closure :
      param * code_loc expr list * env
      -> env se (* lambda (p->e)+ / lazy when param = nil *)
  | Var : _ tagged_expr -> unit se (* set variable, context-insensitive *)
  | Var_sigma : code_loc tagged_expr * env -> env se (* set variable *)
  | App_V : 'a se * arg -> 'a se (* possible values / force when arg = nil *)
  | App_P :
      'a se * arg
      -> 'a se (* possible exn packets / force when arg = nil *)
  | Ctor : ctor * 'a se list -> 'a se (* construct / record field *)
  | Fld : 'a se * 'a fld -> 'a se (* field of a record / deconstruct *)
  | Arith : arithop * 'a se list -> 'a se (* arithmetic operators *)
  | Rel : relop * 'a se list -> 'a se (* relation operators *)
  | Union : 'a se * 'a se -> 'a se (* union *)
  | Inter : 'a se * 'a se -> 'a se (* intersection *)
  | Diff : 'a se * 'a se -> 'a se (* difference *)
  | Cond : 'a se * 'a se -> 'a se (* conditional set expression *)

and rule =
  [ `APP
  | `FORCE
  | `IGNORE
  | `IDENTITY
  | `ARITH
  | `REL
  | `EXTERN
  | `FN
  | `VAR
  | `LET
  | `OP
  | `CON
  | `FIELD
  | `SETFIELD
  | `SEQ
  | `CASE
  | `HANDLE
  | `RAISE
  | `FOR
  | `WHILE ]

let string_of_arithop : arithop -> string = function
  | `ADD -> "+"
  | `SUB -> "-"
  | `DIV -> "÷"
  | `MUL -> "×"
  | `NEG -> "~-"
  | `ABS -> "abs"
  | `MOD -> "mod"
  | `AND -> "&&"
  | `OR -> "||"
  | `NOT -> "not"
  | `XOR -> "xor"
  | `LSL -> "lsl"
  | `LSR -> "lsr"
  | `ASR -> "asr"
  | `SUCC -> "++"
  | `PRED -> "--"

let string_of_relop : relop -> string = function
  | `EQ -> "=="
  | `NE -> "!="
  | `LT -> "<"
  | `LE -> "<="
  | `GT -> ">"
  | `GE -> ">="

let print_param par =
  prerr_string "[";
  let print_pattern pat =
    CL.Printpat.pretty_pat pat;
    prerr_string "; "
  in
  List.iter print_pattern par;
  prerr_string "]"

let print_expr : type k. k expr -> unit = function
  | Expr_var p ->
    prerr_string "Expr_var (";
    print_param p;
    prerr_string ")"
  | Expr loc ->
    prerr_string "Expr (";
    CL.Location.print_loc Format.str_formatter loc;
    prerr_string (Format.flush_str_formatter ());
    prerr_string ")"
  | Extern (s, _) ->
    prerr_string "Extern (";
    prerr_string s;
    prerr_string ")"

let print_tagged_expr : type k. k tagged_expr -> unit = function
  | Val v ->
    prerr_string "Val (";
    print_expr v;
    prerr_string ")"
  | Packet p ->
    prerr_string "Packet (";
    print_expr p;
    prerr_string ")"

let rec print_se : unit se -> unit = function
  | Bot -> prerr_string "⊥"
  | Top -> prerr_string "⊤"
  | Const c -> prerr_string (CL.Printpat.pretty_const c)
  | Fn (p, list) ->
    prerr_string "<";
    print_param p;
    prerr_string "-> [";
    List.iter
      (fun e ->
        print_expr e;
        prerr_string ";")
      list;
    prerr_string "]"
  | Var e ->
    prerr_string "χ (";
    print_tagged_expr e;
    prerr_string ")"
  | App_V (se, list) ->
    prerr_string "AppV (";
    print_se se;
    prerr_string ", [";
    List.iter
      (fun o ->
        (match o with None -> prerr_string " " | Some e -> print_expr e);
        prerr_string ";")
      list;
    prerr_string "]"
  | App_P (se, list) ->
    prerr_string "AppP (";
    print_se se;
    prerr_string ", [";
    List.iter
      (fun o ->
        (match o with None -> prerr_string " " | Some e -> print_expr e);
        prerr_string ";")
      list;
    prerr_string "]"
  | Ctor (k, list) ->
    prerr_string "Con (";
    (match k with None -> prerr_string " " | Some s -> prerr_string s);
    prerr_string ", [";
    List.iter
      (fun se ->
        print_se se;
        prerr_string ";")
      list;
    prerr_string "]"
  | Fld (se, lbl) ->
    prerr_string "Fld (";
    print_se se;
    prerr_string "(";
    (match lbl with
    | None, x ->
      prerr_string " , ";
      print_se x
    | Some s, x ->
      prerr_string s;
      prerr_string ", ";
      print_se x);
    prerr_string "))"
  | Arith (op, xs) ->
    Printf.eprintf "( %s ) " (string_of_arithop op);
    print_ses xs
  | Rel (rel, xs) ->
    Printf.eprintf "( %s ) " (string_of_relop rel);
    print_ses xs
  | Union (x, y) ->
    prerr_string "(";
    print_se x;
    prerr_string ")∪(";
    print_se y;
    prerr_string ")"
  | Inter (x, y) ->
    prerr_string "(";
    print_se x;
    prerr_string ")∩(";
    print_se y;
    prerr_string ")"
  | Diff (x, y) ->
    prerr_string "(";
    print_se x;
    prerr_string ")-(";
    print_se y;
    prerr_string ")"
  | Cond (x, y) ->
    prerr_string "if (";
    print_se x;
    prerr_string ")=∅ then (";
    print_se y;
    prerr_string ") else ∅"

and print_ses (xs : unit se list) =
  prerr_string "[";
  List.iter print_se xs;
  prerr_string "]"

module Param = struct
  type t = param

  let compare = compare
end

module Globalenv = Map.Make (Param)
(** Map chosen to avoid excessive hash collisions due to Param *)

let insensitive_sc : (unit se, unit se) Hashtbl.t = Hashtbl.create 256
let sensitive_sc : (env se, env se) Hashtbl.t = Hashtbl.create 256

type env_map = code_loc tagged_expr Globalenv.t

let show_env_map (env_map : env_map) =
  Globalenv.iter
    (fun param loc_tagged_expr ->
      prerr_string "Globalenv :\n param = ";
      print_param param;
      prerr_string "\n code_loc tagged_expr = ";
      print_tagged_expr loc_tagged_expr;
      prerr_newline ())
    env_map

type globalenv = env_map ref

let globalenv : globalenv = ref Globalenv.empty

type var_se_tbl = unit se CL.Ident.Tbl.t

let show_var_se_tbl (var_to_se : var_se_tbl) =
  CL.Ident.(
    Tbl.iter
      (fun x se ->
        prerr_string "var_to_se :\n ident = ";
        prerr_string (unique_name x);
        prerr_string "\n se = ";
        print_se se;
        prerr_newline ())
      var_to_se)

let var_to_se : var_se_tbl = CL.Ident.Tbl.create 256
let undetermined_var : var_se_tbl = CL.Ident.Tbl.create 64

(* from https://github.com/ocaml/ocaml/blob/1e52236624bad1c80b3c46857723a35c43974297/ocamldoc/odoc_misc.ml#L83 *)
let rec string_of_longident : Longident.t -> string = function
  | CL.Longident.Lident s -> s
  | CL.Longident.Ldot (li, s) -> string_of_longident li ^ "." ^ s
  | CL.Longident.Lapply (l1, l2) ->
    (* applicative functor : see ocamlc -help | grep app-funct *)
    string_of_longident l1 ^ "(" ^ string_of_longident l2 ^ ")"

let string_of_typ : CL.Types.type_desc -> string = function
  | Tvar _ -> "var"
  | Tarrow _ -> "function"
  | Ttuple _ -> "tuple"
  | Tconstr _ -> "construct"
  | Tobject _ -> "object"
  | Tfield _ -> "field"
  | Tnil -> "nil"
  | Tlink _ -> "link"
  | Tsubst _ -> "subst"
  | Tvariant _ -> "variant"
  | Tunivar _ -> "univar"
  | Tpoly _ -> "poly"
  | Tpackage _ -> "package"

let isApply : CL.Types.value_description -> bool = function
  | {val_kind = Val_prim {prim_name = "%apply"}} -> true
  | _ -> false

let isRevapply : CL.Types.value_description -> bool = function
  | {val_kind = Val_prim {prim_name = "%revapply"}} -> true
  | _ -> false

let print_prim : CL.Types.value_description -> unit = function
  | {val_kind = Val_prim {prim_name = s1; prim_native_name = s2}} ->
    Printf.printf "prim_name: %s, prim_native_name: %S\n" s1 s2
  | _ -> ()

let decode : CL.Types.value_description -> rule = function
  | {val_kind = Val_prim {prim_name = s}} -> Primitive.decode_prim s
  | _ -> `APP

let isRaise : CL.Types.value_description -> bool =
 fun v -> match decode v with `RAISE -> true | _ -> false

let updateGlobal key data = globalenv := Globalenv.add key data !globalenv

let extract c =
  let lhs = c.CL.Typedtree.c_lhs in
  let guard = c.CL.Typedtree.c_guard in
  match guard with None -> (lhs, false) | _ -> (lhs, true)

(** add bindings to globalenv when new pattern is introduced *)
let rec updateEnv : CL.Typedtree.expression_desc -> unit = function
  | Texp_let (_, list, _) ->
    let value_bind acc (binding: CL.Typedtree.value_binding) =
      let pattern = binding.vb_pat in
      let expr = Val (Expr binding.vb_expr.exp_loc) in
      solveEq pattern (Var expr) |> ignore;
      updateGlobal [pattern] expr
    in
    List.fold_left value_bind () list
  | Texp_function {cases} ->
    let value_pg = List.map extract cases in
    let value_p, _ = List.split value_pg in
    let value_expr = Val (Expr_var value_p) in
    List.fold_left solveParam (Var value_expr) value_pg |> ignore
#if OCAML_VERSION < (4, 08, 0)
  | Texp_match (exp, cases, exn_cases, _) ->
    let value_pg = List.map extract cases in
    let exn_pg = List.map extract exn_cases in
    let value_p, _ = List.split value_pg in
    let exn_p, _ = List.split exn_pg in
    let value_expr = Val (Expr exp.exp_loc) in
    let exn_expr = Packet (Expr exp.exp_loc) in
    updateGlobal value_p value_expr;
    List.fold_left solveParam (Var value_expr) value_pg |> ignore;
    updateGlobal exn_p exn_expr;
    List.fold_left solveParam (Var exn_expr) exn_pg |> ignore
#else
  | Texp_match (exp, cases, _) ->
    let p, g = List.split @@ List.map extract cases in
    let o = List.map Typedtree.split_pattern p in
    let rec filter o g =
      match o with
      | (Some v, Some e) :: o' -> (
        match g with
        | b :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v :: v_p, b :: v_g, e :: e_p, b :: e_g)
        | _ -> assert false)
      | (Some v, None) :: o' -> (
        match g with
        | b :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v :: v_p, b :: v_g, e_p, e_g)
        | _ -> assert false)
      | (None, Some e) :: o' -> (
        match g with
        | b :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v_p, v_g, e :: e_p, b :: e_g)
        | _ -> assert false)
      | (None, None) :: o' -> (
        match g with
        | b :: g' ->
          let v_p, v_g, e_p, e_g = filter o' g' in
          (v_p, v_g, e_p, e_g)
        | _ -> assert false)
      | [] -> ([], [], [], [])
    in
    let value_p, value_g, exn_p, exn_g = filter o g in
    let value_expr = Val (Expr exp.exp_loc) in
    let exn_expr = Packet (Expr exp.exp_loc) in
    updateGlobal value_p value_expr;
    List.fold_left solveParam (Var value_expr) (List.combine value_p value_g)
    |> ignore;
    updateGlobal exn_p exn_expr;
    List.fold_left solveParam (Var exn_expr) (List.combine exn_p exn_g)
    |> ignore
#endif
  | Texp_try (exp, cases) ->
    let exn_pg = List.map extract cases in
    let exn_p, _ = List.split exn_pg in
    let exn_expr = Packet (Expr exp.exp_loc) in
    updateGlobal exn_p exn_expr;
    List.fold_left solveParam (Var exn_expr) exn_pg |> ignore
  | _ -> ()

(** solves p_i = acc, that is, p_1 = se; p_2 = se - p_1; ... *)
and solveParam (acc : unit se) (pattern, guarded) =
  if guarded then (
    solveEq pattern acc |> ignore;
    acc)
  else Diff (acc, solveEq pattern acc)

and updateVar key data =
  if CL.Ident.Tbl.mem var_to_se key then (
    let original = CL.Ident.Tbl.find var_to_se key in
    CL.Ident.Tbl.remove var_to_se key;
    CL.Ident.Tbl.add var_to_se key (Union (data, original)))
  else CL.Ident.Tbl.add var_to_se key data

and se_of_int n = Const (CL.Asttypes.Const_int n)

(** solves p = se and returns the set expression for p *)
and solveEq (p : CL.Typedtree.pattern) (se : unit se) : unit se =
  match p.pat_desc with
  | Tpat_any -> Top
  | Tpat_var (x, _) ->
    updateVar x se;
    Top
  | Tpat_alias (p, a, _) ->
    updateVar a se;
    solveEq p se
  | Tpat_constant c -> Const c
  | Tpat_tuple list -> solveCtor None se list
#if OCAML_VERSION >= (4, 13, 0)
  | Tpat_construct ({txt}, _, list, _) ->
#else
  | Tpat_construct ({txt}, _, list) ->
#endif
    let constructor = string_of_longident txt in
    solveCtor (Some constructor) se list
  | Tpat_variant (lbl, p_o, _) -> (
    let constructor = Some lbl in
    match p_o with
    | None -> Ctor (constructor, [Top]) (* hash of the variant name *)
    | Some p ->
      let sub = solveEq p (Fld (se, (constructor, se_of_int 1))) in
      Ctor (constructor, [Top; sub]))
  | Tpat_record (key_val_list, _) ->
    let list =
      List.map (fun (_, lbl, pat) -> (lbl.CL.Types.lbl_pos, pat)) key_val_list
    in
    let lbl_all = (match key_val_list with
      | (_, {CL.Types.lbl_all = l}, _) :: _ -> l
      | _ -> failwith "NO!!") in
    let len = Array.length lbl_all in
    solveRec len se list
  | Tpat_array list -> solveCtor None se list
  | Tpat_lazy p -> solveEq p (App_V (se, []))
  | Tpat_or (lhs, rhs, _) -> Union (solveEq lhs se, solveEq rhs se)

and solveCtor constructor se list =
  let l = ref list in
  let args = ref [] in
  let i = ref 0 in
  while !l != [] do
    (match !l with
    | hd :: tl ->
      let ith_se = solveEq hd (Fld (se, (constructor, se_of_int !i))) in
      args := ith_se :: !args;
      l := tl
    | _ -> assert false);
    i := !i + 1
  done;
  Ctor (constructor, List.rev !args)

and solveRec len se list =
  let l = ref list in
  let args = ref [] in
  let cursor = ref 0 in
  while !l != [] do
    match !l with
    | hd :: tl ->
      let i, p = hd in
      let ith_se = solveEq p (Fld (se, (None, se_of_int i))) in
      while !cursor < i do
        args := Top :: !args;
        cursor := !cursor + 1
      done;
      args := ith_se :: !args;
      l := tl
    | _ -> assert false
  done;
  while !cursor < len do
    args := Top :: !args;
    cursor := !cursor + 1
  done;
  Ctor (None, List.rev !args)

let rec generateSC : rule -> CL.Typedtree.expression_desc -> unit = function
  | `APP -> (
    function
    | Texp_apply ({exp_desc = Texp_ident (_, _, atat)}, [(_, Some fn); arg])
      when (* f @@ x *)
           atat |> isApply ->
      generateSC `APP (Texp_apply (fn, [arg]))
    | Texp_apply ({exp_desc = Texp_ident (_, _, atat)}, [arg; (_, Some fn)])
      when (* x |> f *)
           atat |> isRevapply ->
      generateSC `APP (Texp_apply (fn, [arg]))
    | Texp_apply (fn, arg) -> ()
    | Texp_lazy e -> ()
    | _ -> failwith "Tried to apply APP rule for the wrong expression!")
  | `FORCE | `IGNORE | `IDENTITY | `ARITH | `REL | `EXTERN | `FN | `VAR | `LET
  | `OP | `CON | `FIELD | `SETFIELD -> (
    function Texp_apply (a, b) -> () | _ -> ())
  | `SEQ | `CASE | `HANDLE | `RAISE | `FOR | `WHILE -> fun e -> ()

let rec augmentSC : unit se -> env se = function _ -> Top
let posToString = Common.posToString

let print_sc_info () =
  show_env_map !globalenv;
  show_var_se_tbl var_to_se

module LocSet = Common.LocSet

module Values = struct
  let valueBindingsTable =
    (Hashtbl.create 15 : (string, (string, Exceptions.t) Hashtbl.t) Hashtbl.t)

  let currentFileTable = ref (Hashtbl.create 1)

  let add ~name exceptions =
    let path = (name |> Name.create) :: (ModulePath.getCurrent ()).path in
    Hashtbl.replace !currentFileTable (path |> Common.Path.toString) exceptions

  let getFromModule ~moduleName ~modulePath (path_ : Common.Path.t) =
    let name = path_ @ modulePath |> Common.Path.toString in
    match
      Hashtbl.find_opt valueBindingsTable (String.capitalize_ascii moduleName)
    with
    | Some tbl -> Hashtbl.find_opt tbl name
    | None -> (
      match
        Hashtbl.find_opt valueBindingsTable
          (String.uncapitalize_ascii moduleName)
      with
      | Some tbl -> Hashtbl.find_opt tbl name
      | None -> None)

  let rec findLocal ~moduleName ~modulePath path =
    match path |> getFromModule ~moduleName ~modulePath with
    | Some exceptions -> Some exceptions
    | None -> (
      match modulePath with
      | [] -> None
      | _ :: restModulePath ->
        path |> findLocal ~moduleName ~modulePath:restModulePath)

  let findPath ~moduleName ~modulePath path =
    let findExternal ~externalModuleName ~pathRev =
      pathRev |> List.rev
      |> getFromModule
           ~moduleName:(externalModuleName |> Name.toString)
           ~modulePath:[]
    in
    match path |> findLocal ~moduleName ~modulePath with
    | None -> (
      (* Search in another file *)
      match path |> List.rev with
      | externalModuleName :: pathRev -> (
        match (findExternal ~externalModuleName ~pathRev, pathRev) with
        | (Some _ as found), _ -> found
        | None, externalModuleName2 :: pathRev2
          when !Common.Cli.cmtCommand && pathRev2 <> [] ->
          (* Simplistic namespace resolution for dune namespace: skip the root of the path *)
          findExternal ~externalModuleName:externalModuleName2 ~pathRev:pathRev2
        | None, _ -> None)
      | [] -> None)
    | Some exceptions -> Some exceptions

  let newCmt () =
    currentFileTable := Hashtbl.create 15;
    Hashtbl.replace valueBindingsTable !Common.currentModule !currentFileTable
end

(* module SetConstraintEvent = struct
     type t = {
       globalEnv : globalenv;
       var_to_se : unit se CL.Ident.Tbl.t;
       loc : CL.Location.t
     } [@@derving show]
   end *)

module Event = struct
  type kind =
    | Catches of t list (* with | E => ... *)
    | Call of {callee : Common.Path.t; modulePath : Common.Path.t} (* foo() *)
    | DoesNotRaise of
        t list (* DoesNotRaise(events) where events come from an expression *)
    | Raises  (** raise E *)

  and t = {exceptions : Exceptions.t; kind : kind; loc : CL.Location.t}

  let rec print ppf event =
    match event with
    | {kind = Call {callee; modulePath}; exceptions; loc} ->
      Format.fprintf ppf "%s Call(%s, modulePath:%s) %a@."
        (loc.loc_start |> posToString)
        (callee |> Common.Path.toString)
        (modulePath |> Common.Path.toString)
        (Exceptions.pp ~exnTable:None)
        exceptions
    | {kind = DoesNotRaise nestedEvents; loc} ->
      Format.fprintf ppf "%s DoesNotRaise(%a)@."
        (loc.loc_start |> posToString)
        (fun ppf () ->
          nestedEvents |> List.iter (fun e -> Format.fprintf ppf "%a " print e))
        ()
    | {kind = Raises; exceptions; loc} ->
      Format.fprintf ppf "%s raises %a@."
        (loc.loc_start |> posToString)
        (Exceptions.pp ~exnTable:None)
        exceptions
    | {kind = Catches nestedEvents; exceptions; loc} ->
      Format.fprintf ppf "%s Catches exceptions:%a nestedEvents:%a@."
        (loc.loc_start |> posToString)
        (Exceptions.pp ~exnTable:None)
        exceptions
        (fun ppf () ->
          nestedEvents |> List.iter (fun e -> Format.fprintf ppf "%a " print e))
        ()

  let combine ~moduleName events =
    if !Common.Cli.debug then (
      Log_.item "@.";
      Log_.item "Events combine: #events %d@." (events |> List.length));
    let exnTable = Hashtbl.create 1 in
    let extendExnTable exn loc =
      match Hashtbl.find_opt exnTable exn with
      | Some locSet -> Hashtbl.replace exnTable exn (LocSet.add loc locSet)
      | None -> Hashtbl.replace exnTable exn (LocSet.add loc LocSet.empty)
    in
    let shrinkExnTable exn loc =
      match Hashtbl.find_opt exnTable exn with
      | Some locSet -> Hashtbl.replace exnTable exn (LocSet.remove loc locSet)
      | None -> ()
    in
    let rec loop exnSet events =
      match events with
      | ({kind = Raises; exceptions; loc} as ev) :: rest ->
        if !Common.Cli.debug then Log_.item "%a@." print ev;
        exceptions |> Exceptions.iter (fun exn -> extendExnTable exn loc);
        loop (Exceptions.union exnSet exceptions) rest
      | ({kind = Call {callee; modulePath}; loc} as ev) :: rest ->
        if !Common.Cli.debug then Log_.item "%a@." print ev;
        let exceptions =
          match callee |> Values.findPath ~moduleName ~modulePath with
          | Some exceptions -> exceptions
          | _ -> (
            match ExnLib.find callee with
            | Some exceptions -> exceptions
            | None -> Exceptions.empty)
        in
        exceptions |> Exceptions.iter (fun exn -> extendExnTable exn loc);
        loop (Exceptions.union exnSet exceptions) rest
      | ({kind = DoesNotRaise nestedEvents; loc} as ev) :: rest ->
        if !Common.Cli.debug then Log_.item "%a@." print ev;
        let nestedExceptions = loop Exceptions.empty nestedEvents in
        (if Exceptions.isEmpty nestedExceptions (* catch-all *) then
         let name =
           match nestedEvents with
           | {kind = Call {callee}} :: _ -> callee |> Common.Path.toString
           | _ -> "expression"
         in
         Log_.warning ~loc ~name:"Exception Analysis" (fun ppf () ->
             Format.fprintf ppf
               "@{<info>%s@} does not raise and is annotated with redundant \
                @doesNotRaise"
               name));
        loop exnSet rest
      | ({kind = Catches nestedEvents; exceptions} as ev) :: rest ->
        if !Common.Cli.debug then Log_.item "%a@." print ev;
        if Exceptions.isEmpty exceptions then loop exnSet rest
        else
          let nestedExceptions = loop Exceptions.empty nestedEvents in
          let newRaises = Exceptions.diff nestedExceptions exceptions in
          exceptions
          |> Exceptions.iter (fun exn ->
                 nestedEvents
                 |> List.iter (fun event -> shrinkExnTable exn event.loc));
          loop (Exceptions.union exnSet newRaises) rest
      | [] -> exnSet
    in
    let exnSet = loop Exceptions.empty events in
    (exnSet, exnTable)
end

module Checks = struct
  type check = {
    (* scEvents : SetConstraintEvent.t list; *)
    events : Event.t list;
    loc : CL.Location.t;
    locFull : CL.Location.t;
    moduleName : string;
    name : string;
    exceptions : Exceptions.t;
  }

  type t = check list

  let checks = (ref [] : t ref)

  let add ~events ~exceptions ~loc ?(locFull = loc) ~moduleName name =
    checks := {events; exceptions; loc; locFull; moduleName; name} :: !checks

  let doCheck {events; exceptions; loc; locFull; moduleName; name} =
    let raiseSet, exnTable = events |> Event.combine ~moduleName in
    let missingAnnotations = Exceptions.diff raiseSet exceptions in
    let redundantAnnotations = Exceptions.diff exceptions raiseSet in
    if not (Exceptions.isEmpty missingAnnotations) then (
      let raisesTxt =
        Format.asprintf "%a" (Exceptions.pp ~exnTable:(Some exnTable)) raiseSet
      in
      let missingTxt =
        Format.asprintf "%a" (Exceptions.pp ~exnTable:None) missingAnnotations
      in
      Log_.warning ~loc ~name:"Exception Analysis" ~notClosed:true
        (fun ppf () ->
          Format.fprintf ppf
            "@{<info>%s@} might raise %s and is not annotated with @raises(%s)"
            name raisesTxt missingTxt);
      if !Common.Cli.json then (
        EmitJson.emitAnnotate ~action:"Add @raises annotation"
          ~pos:(EmitJson.locToPos locFull)
          ~text:(Format.asprintf "@raises(%s)\\n" missingTxt);
        EmitJson.emitClose ()));
    if not (Exceptions.isEmpty redundantAnnotations) then
      Log_.warning ~loc ~name:"Exception Analysis" (fun ppf () ->
          let raisesDescription ppf () =
            if raiseSet |> Exceptions.isEmpty then
              Format.fprintf ppf "raises nothing"
            else
              Format.fprintf ppf "might raise %a"
                (Exceptions.pp ~exnTable:(Some exnTable))
                raiseSet
          in
          Format.fprintf ppf
            "@{<info>%s@} %a and is annotated with redundant @raises(%a)" name
            raisesDescription ()
            (Exceptions.pp ~exnTable:None)
            redundantAnnotations)

  let doChecks () = !checks |> List.rev |> List.iter doCheck
end

let traverseAst () =
  ModulePath.init ();
  let super = CL.Tast_mapper.default in
  let currentId = ref "" in
  let currentEvents = ref [] in
  let exceptionsOfPatterns patterns =
    patterns
    |> List.fold_left
         (fun acc desc ->
           match desc with
           | CL.Typedtree.Tpat_construct _ ->
             Exceptions.add (Exn.fromLid (Compat.unboxPatCstrTxt desc)) acc
           | _ -> acc)
         Exceptions.empty
  in
  let iterExpr self e = self.CL.Tast_mapper.expr self e |> ignore in
  let iterExprOpt self eo =
    match eo with None -> () | Some e -> e |> iterExpr self
  in
  let iterPat self p = self.CL.Tast_mapper.pat self p |> ignore in
  let iterCases self cases =
    cases
    |> List.iter (fun case ->
           case.CL.Typedtree.c_lhs |> iterPat self;
           case.c_guard |> iterExprOpt self;
           case.c_rhs |> iterExpr self)
  in
  let raiseArgs args =
    match args with
    | [(_, Some {CL.Typedtree.exp_desc = Texp_construct ({txt}, _, _)})] ->
      [Exn.fromLid txt] |> Exceptions.fromList
    | [(_, Some {CL.Typedtree.exp_desc = Texp_ident _})] ->
      [Exn.fromString "genericException"] |> Exceptions.fromList
    | _ -> [Exn.fromString "TODO_from_raise1"] |> Exceptions.fromList
  in
  let doesNotRaise attributes =
    attributes
    |> Annotation.getAttributePayload (fun s ->
           s = "doesNotRaise" || s = "doesnotraise" || s = "DoesNoRaise"
           || s = "doesNotraise" || s = "doNotRaise" || s = "donotraise"
           || s = "DoNoRaise" || s = "doNotraise")
    <> None
  in
  let expr (self : CL.Tast_mapper.mapper) (expr : CL.Typedtree.expression) =
    let loc = expr.exp_loc in
    let isDoesNoRaise = expr.exp_attributes |> doesNotRaise in
    let oldEvents = !currentEvents in
    if isDoesNoRaise then currentEvents := [];

    (* Generate SCs  *)
    updateEnv expr.exp_desc;

    (match expr.exp_desc with
    | Texp_ident (callee_, _, val_desc) ->
      let callee =
        callee_ |> Common.Path.fromPathT |> ModulePath.resolveAlias
      in
      let calleeName = callee |> Common.Path.toString in
      if val_desc |> isRaise then
        Log_.warning ~loc ~name:"Exception Analysis" (fun ppf () ->
            Format.fprintf ppf
              "@{<info>%s@} can be analyzed only if called directly" calleeName);
      currentEvents :=
        {
          Event.exceptions = Exceptions.empty;
          loc;
          kind = Call {callee; modulePath = (ModulePath.getCurrent ()).path};
        }
        :: !currentEvents
    | Texp_apply
        ( {exp_desc = Texp_ident (_, _, atat)},
          [(_lbl1, Some {exp_desc = Texp_ident (_, _, val_desc)}); arg] )
      when (* raise @@ Exn(...) *)
           atat |> isApply && val_desc |> isRaise ->
      let exceptions = [arg] |> raiseArgs in
      currentEvents := {Event.exceptions; loc; kind = Raises} :: !currentEvents;
      arg |> snd |> iterExprOpt self
    | Texp_apply
        ( {exp_desc = Texp_ident (_, _, atat)},
          [arg; (_lbl1, Some {exp_desc = Texp_ident (_, _, val_desc)})] )
      when (*  Exn(...) |> raise *)
           atat |> isRevapply && val_desc |> isRaise ->
      let exceptions = [arg] |> raiseArgs in
      currentEvents := {Event.exceptions; loc; kind = Raises} :: !currentEvents;
      arg |> snd |> iterExprOpt self
    | Texp_apply (({exp_desc = Texp_ident (_, _, val_desc)} as e), args) ->
      if val_desc |> isRaise then
        let exceptions = args |> raiseArgs in
        currentEvents :=
          {Event.exceptions; loc; kind = Raises} :: !currentEvents
      else e |> iterExpr self;
      args |> List.iter (fun (_, eOpt) -> eOpt |> iterExprOpt self)
    | Texp_match _ ->
      let e, cases, partial = Compat.getTexpMatch expr.exp_desc in
      let exceptionPatterns = expr.exp_desc |> Compat.texpMatchGetExceptions in
      let exceptions = exceptionPatterns |> exceptionsOfPatterns in
      if exceptionPatterns <> [] then (
        let oldEvents = !currentEvents in
        currentEvents := [];
        e |> iterExpr self;
        currentEvents :=
          {Event.exceptions; loc; kind = Catches !currentEvents} :: oldEvents)
      else e |> iterExpr self;
      cases |> iterCases self;
      if partial = Partial then
        currentEvents :=
          {
            Event.exceptions = [Exn.matchFailure] |> Exceptions.fromList;
            loc;
            kind = Raises;
          }
          :: !currentEvents
    | Texp_try (e, cases) ->
      let exceptions =
        cases
        |> List.map (fun case -> case.CL.Typedtree.c_lhs.pat_desc)
        |> exceptionsOfPatterns
      in
      let oldEvents = !currentEvents in
      currentEvents := [];
      e |> iterExpr self;
      currentEvents :=
        {Event.exceptions; loc; kind = Catches !currentEvents} :: oldEvents;
      cases |> iterCases self
    | _ -> super.expr self expr |> ignore);
    (if isDoesNoRaise then
     let nestedEvents = !currentEvents in
     currentEvents :=
       {
         Event.exceptions = Exceptions.empty;
         loc;
         kind = DoesNotRaise nestedEvents;
       }
       :: oldEvents);
    expr
  in
  let getExceptionsFromAnnotations attributes =
    let raisesAnnotationPayload =
      attributes
      |> Annotation.getAttributePayload (fun s -> s = "raises" || s = "raise")
    in
    let rec getExceptions payload =
      match payload with
      | Annotation.StringPayload s -> [Exn.fromString s] |> Exceptions.fromList
      | Annotation.ConstructPayload s when s <> "::" ->
        [Exn.fromString s] |> Exceptions.fromList
      | Annotation.IdentPayload s ->
        [Exn.fromString (s |> CL.Longident.flatten |> String.concat ".")]
        |> Exceptions.fromList
      | Annotation.TuplePayload tuple ->
        tuple
        |> List.map (fun payload ->
               payload |> getExceptions |> Exceptions.toList)
        |> List.concat |> Exceptions.fromList
      | _ -> Exceptions.empty
    in
    match raisesAnnotationPayload with
    | None -> Exceptions.empty
    | Some payload -> payload |> getExceptions
  in
  let toplevelEval (self : CL.Tast_mapper.mapper)
      (expr : CL.Typedtree.expression) attributes =
    let oldId = !currentId in
    let oldEvents = !currentEvents in
    let name = "Toplevel expression" in
    currentId := name;
    currentEvents := [];
    let moduleName = !Common.currentModule in
    self.expr self expr |> ignore;
    Checks.add ~events:!currentEvents
      ~exceptions:(getExceptionsFromAnnotations attributes)
      ~loc:expr.exp_loc ~moduleName name;
    currentId := oldId;
    currentEvents := oldEvents
  in
  let structure_item (self : CL.Tast_mapper.mapper)
      (structureItem : CL.Typedtree.structure_item) =
    let oldModulePath = ModulePath.getCurrent () in
    (match structureItem.str_desc with
    | Tstr_eval (expr, attributes) -> toplevelEval self expr attributes
    | Tstr_module {mb_id; mb_loc} ->
      ModulePath.setCurrent
        {
          oldModulePath with
          loc = mb_loc;
          path =
            (mb_id |> Compat.moduleIdName |> Name.create) :: oldModulePath.path;
        }
    | _ -> ());
    let result = super.structure_item self structureItem in
    ModulePath.setCurrent oldModulePath;
    (match structureItem.str_desc with
    | Tstr_module {mb_id; mb_expr = {mod_desc = Tmod_ident (path_, _lid)}} ->
      ModulePath.addAlias
        ~name:(mb_id |> Compat.moduleIdName |> Name.create)
        ~path:(path_ |> Common.Path.fromPathT)
    | _ -> ());
    result
  in
  let value_binding (self : CL.Tast_mapper.mapper)
      (vb : CL.Typedtree.value_binding) =
    let oldId = !currentId in
    let oldEvents = !currentEvents in
    let isFunction =
      match vb.vb_expr.exp_desc with Texp_function _ -> true | _ -> false
    in
    let isToplevel = !currentId = "" in
    let processBinding name =
      currentId := name;
      currentEvents := [];
      let exceptionsFromAnnotations =
        getExceptionsFromAnnotations vb.vb_attributes
      in
      exceptionsFromAnnotations |> Values.add ~name;
      let res = super.value_binding self vb in
      let moduleName = !Common.currentModule in
      let path = [name |> Name.create] in
      let exceptions =
        match
          path
          |> Values.findPath ~moduleName
               ~modulePath:(ModulePath.getCurrent ()).path
        with
        | Some exceptions -> exceptions
        | _ -> Exceptions.empty
      in
      Checks.add ~events:!currentEvents ~exceptions ~loc:vb.vb_pat.pat_loc
        ~locFull:vb.vb_loc ~moduleName name;
      currentId := oldId;
      currentEvents := oldEvents;
      res
    in
    match vb.vb_pat.pat_desc with
    | Tpat_any when isToplevel && not vb.vb_loc.loc_ghost -> processBinding "_"
    | Tpat_construct _
      when isToplevel && (not vb.vb_loc.loc_ghost)
           && Compat.unboxPatCstrTxt vb.vb_pat.pat_desc
              = CL.Longident.Lident "()" ->
      processBinding "()"
    | Tpat_var (id, {loc = {loc_ghost}})
      when (isFunction || isToplevel) && (not loc_ghost)
           && not vb.vb_loc.loc_ghost ->
      processBinding (id |> CL.Ident.name)
    | _ -> super.value_binding self vb
  in
  let open CL.Tast_mapper in
  {super with expr; value_binding; structure_item}

let processStructure (structure : CL.Typedtree.structure) =
  let traverseAst = traverseAst () in
  structure |> traverseAst.structure traverseAst |> ignore;
  (if !Common.Cli.debug then print_sc_info ())

let processCmt (cmt_infos : CL.Cmt_format.cmt_infos) =
  match cmt_infos.cmt_annots with
  | Interface _ -> ()
  | Implementation structure ->
    Values.newCmt ();
    structure |> processStructure
  | _ -> ()

let reportResults ~ppf:_ = Checks.doChecks ()
