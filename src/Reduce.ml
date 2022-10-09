open SetExpression

exception Not_resolvable

let resolve_as_const : unit se -> CL.Asttypes.constant = function
  | Arith (INT ADD, [_; _]) -> Const_char 'c'
  | Arith (INT SUB, [_; _]) -> Const_float "1.0"
  | Arith (INT DIV, [_; _]) -> Const_int 1
  | Arith (INT MUL, [_; _]) -> Const_int32 1l
  | Arith (INT NEG, [_; _]) -> Const_int64 2L
  | Arith (FLOAT ABS, [_]) (* absolute value *) | Arith (INT MOD, [_; _]) ->
    Const_nativeint 0n
  | Arith (INT AND, [_; _])
  | Arith (INT OR, [_; _])
  | Arith (INT NOT, [_; _])
  | Arith (INT XOR, [_; _])
  | Arith (INT LSL, [_; _]) (* <<, logical *)
  | Arith (INT LSR, [_; _]) (* >>, logical *)
  | Arith (INT ASR, [_; _]) ->
    Const_int 1 (* >>, arithmetic sign extension *)
  | Arith (INT SUCC, [_]) (* ++x *) | Arith (INT PRED, [_]) ->
    Const_int 1 (* --x *)
  | _ -> Const_int 1

let resolve_arith : unit se -> unit se =
 fun e -> try Const (resolve_as_const e) with Not_resolvable -> Top

let decode_prim = function
  | "%identity" | "%bytes_to_string" | "%bytes_of_string" -> `IDENTITY
  | "%intoffloat" | "%floatofint" -> `IDENTITY
  | "%nativeint_of_int" | "%nativeint_to_int" -> `IDENTITY
  | "%int32_of_int" | "%int32_to_int" -> `IDENTITY
  | "%int64_of_int" | "%int64_to_int" | "%opaque" -> `IDENTITY
  | "%nativeint_of_int32" | "%nativeint_to_int32" | "%int64_of_int32"
  | "%int64_to_int32" | "%int64_of_nativeint" | "%int64_to_nativeint" ->
    `IDENTITY
  | "%bswap16" | "%bswap_int32" | "%bswap_int64" | "%bswap_native" -> `ARITH
  | "%ignore" -> `IGNORE
  | "%revapply" | "%apply" -> `APP
  | "%loc_LOC" | "%loc_FILE" | "%loc_LINE" | "%loc_" | "%loc_MODULE"
  | "%loc_FUNCTION" ->
    `EXTERN
  | "%field0" | "%field1" -> `FIELD
  | "%setfield0" -> `SETFIELD
  | "%makeblock" | "%makemutable" -> `CON
  | "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace" -> `RAISE
  | "%sequand" | "%sequor" | "%boolnot" | "%negint" | "%succint" | "%predint"
  | "%addint" | "%subint" | "%mulint" | "%divint" | "%modint" | "%andint"
  | "%orint" | "%xorint" | "%lslint" | "%lsrint" | "%asrint" ->
    `ARITH
  | "%eq" | "%noteq" | "%ltint" | "%leint" | "%gtint" | "%geint" -> `REL
  | "%incr" | "%decr" -> `SETFIELD
  | "%negfloat" | "%absfloat" | "%addfloat" | "%subfloat" | "%mulfloat"
  | "%divfloat" ->
    `ARITH
  | "%eqfloat" | "%noteqfloat" | "%ltfloat" | "%lefloat" | "%gtfloat"
  | "%gefloat" ->
    `REL
  | "%string_length" | "%bytes_length" | "%array_length" | "%obj_size"
  | "%floatarray_length" ->
    `EXTERN
  | "%string_safe_get" | "%string_unsafe_get" | "%bytes_safe_get"
  | "%bytes_unsafe_get" | "%array_safe_get" | "%array_unsafe_get" | "%obj_field"
  | "%floatarray_unsafe_get" | "%floatarray_safe_get" ->
    `FIELD
  | "%string_safe_set" | "%string_unsafe_set" | "%bytes_safe_set"
  | "%bytes_unsafe_set" | "%array_safe_set" | "%array_unsafe_set"
  | "%obj_set_field" | "%floatarray_unsafe_set" | "%floatarray_safe_set" ->
    `SETFIELD
  | "%lazy_force" -> `FORCE
  | "%nativeint_neg" | "%nativeint_add" | "%nativeint_sub" | "%nativeint_mul"
  | "%nativeint_div" | "%nativeint_mod" | "%nativeint_and" | "%nativeint_or"
  | "%nativeint_xor" | "%nativeint_lsl" | "%nativeint_lsr" | "%nativeint_asr" ->
    `ARITH
  | "%int32_neg" | "%int32_add" | "%int32_sub" | "%int32_mul" | "%int32_div"
  | "%int32_mod" | "%int32_and" | "%int32_or" | "%int32_xor" | "%int32_lsl"
  | "%int32_lsr" | "%int32_asr" ->
    `ARITH
  | "%int64_neg" | "%int64_add" | "%int64_sub" | "%int64_mul" | "%int64_div"
  | "%int64_mod" | "%int64_and" | "%int64_or" | "%int64_xor" | "%int64_lsl"
  | "%int64_lsr" | "%int64_asr" ->
    `ARITH
  | "%caml_ba_ref_1" | "%caml_ba_ref_2" | "%caml_ba_ref_3" -> `FIELD
  | "%caml_ba_set_1" | "%caml_ba_set_2" | "%caml_ba_set_3" -> `SETFIELD
  | "%caml_ba_unsafe_ref_1" | "%caml_ba_unsafe_ref_2" | "%caml_ba_unsafe_ref_3"
    ->
    `FIELD
  | "%caml_ba_unsafe_set_1" | "%caml_ba_unsafe_set_2" | "%caml_ba_unsafe_set_3"
    ->
    `SETFIELD
  | "%caml_ba_dim_1" | "%caml_ba_dim_2" | "%caml_ba_dim_3" -> `EXTERN
  | "%caml_string_get16" | "%caml_string_get16u" | "%caml_string_get32"
  | "%caml_string_get32u" | "%caml_string_get64" | "%caml_string_get64u" ->
    `FIELD
  | "%caml_string_set16" | "%caml_string_set16u" | "%caml_string_set32"
  | "%caml_string_set32u" | "%caml_string_set64" | "%caml_string_set64u" ->
    `SETFIELD
  | "%caml_bytes_get16" | "%caml_bytes_get16u" | "%caml_bytes_get32"
  | "%caml_bytes_get32u" | "%caml_bytes_get64" | "%caml_bytes_get64u" ->
    `FIELD
  | "%caml_bytes_set16" | "%caml_bytes_set16u" | "%caml_bytes_set32"
  | "%caml_bytes_set32u" | "%caml_bytes_set64" | "%caml_bytes_set64u" ->
    `SETFIELD
  | "%caml_bigstring_get16" | "%caml_bigstring_get16u" | "%caml_bigstring_get32"
  | "%caml_bigstring_get32u" | "%caml_bigstring_get64"
  | "%caml_bigstring_get64u" ->
    `FIELD
  | "%caml_bigstring_set16" | "%caml_bigstring_set16u" | "%caml_bigstring_set32"
  | "%caml_bigstring_set32u" | "%caml_bigstring_set64"
  | "%caml_bigstring_set64u" ->
    `SETFIELD
  | "%sys_argv" -> `EXTERN
  | "%send" | "%sendself" | "%sendcache" -> `FIELD
  | "%equal" | "%notequal" | "%lessequal" | "%lessthan" | "%greaterequal"
  | "%greaterthan" | "%compare" ->
    `REL
  | "%atomic_load" -> `FIELD
  | "%atomic_exchange" | "%atomic_cas" | "%atomic_fetch_add" -> `SETFIELD
  | "%runstack" | "%reperform" | "%perform" | "%resume" (* effects *)
  | "%dls_get" (* domain-local-state *) | _ ->
    `EXTERN

let c_changed = ref false
let g_changed = ref false

module GE = struct
  type t = pattern se

  let compare = compare
end

module GESet = Set.Make (GE)

let update_c key set =
  if Hashtbl.mem sc key then (
    let original = Hashtbl.find sc key in
    let diff = SESet.diff set original in
    if SESet.is_empty diff then () else Hashtbl.remove sc key;
    Hashtbl.add sc key (SESet.union original set);
    c_changed := true)
  else Hashtbl.add sc key set;
  c_changed := true

let update_loc key set =
  if Hashtbl.mem mem key then (
    let original = Hashtbl.find mem key in
    let diff = SESet.diff set original in
    if SESet.is_empty diff then () else Hashtbl.remove mem key;
    Hashtbl.add mem key (SESet.union original set);
    c_changed := true)
  else Hashtbl.add mem key set;
  c_changed := true

let grammar : (pattern se, GESet.t) Hashtbl.t = Hashtbl.create 256

let update_g key set =
  if Hashtbl.mem grammar key then (
    let original = Hashtbl.find grammar key in
    let diff = GESet.diff set original in
    if GESet.is_empty diff then () else Hashtbl.remove grammar key;
    Hashtbl.add grammar key (GESet.union original diff);
    g_changed := true)
  else Hashtbl.add grammar key set;
  g_changed := true

let abs_mem : (int, GESet.t) Hashtbl.t = Hashtbl.create 256

let update_abs_loc key set =
  if Hashtbl.mem abs_mem key then (
    let original = Hashtbl.find abs_mem key in
    let diff = GESet.diff set original in
    if GESet.is_empty diff then () else Hashtbl.remove abs_mem key;
    Hashtbl.add abs_mem key (GESet.union original set);
    g_changed := true)
  else Hashtbl.add abs_mem key set;
  g_changed := true

let rec arg_len = function
  | [] -> 0
  | None :: tl -> arg_len tl
  | Some _ :: tl -> arg_len tl + 1

let rec merge_args = function
  | [], l -> l
  | l, [] -> l
  | None :: tl, hd :: l -> hd :: merge_args (tl, l)
  | Some x :: tl, l -> Some x :: merge_args (tl, l)

let rec filter_pat = function
  | _, Top -> GESet.empty
  | x, p when x = p -> GESet.empty
  | x, Const c when x != Const c -> GESet.singleton x
  | (Ctor_pat (kappa, _) as x), Ctor_pat (kappa', _) when kappa != kappa' ->
    GESet.singleton x
  | Top, Ctor_pat (kappa, arr) ->
    filter_pat
      (Ctor_pat (kappa, Array.map (fun _ -> Top) arr), Ctor_pat (kappa, arr))
  | Var x, p when Hashtbl.mem grammar (Var x) ->
    GESet.fold
      (fun y acc -> GESet.union (filter_pat (y, p)) acc)
      (Hashtbl.find grammar (Var x))
      GESet.empty
  | Loc (l, None), p when Hashtbl.mem abs_mem l ->
    GESet.map
      (fun x -> Loc (l, Some x))
      (GESet.fold
         (fun y acc -> GESet.union (filter_pat (y, p)) acc)
         (Hashtbl.find abs_mem l) GESet.empty)
  | Loc (l, Some p), p' ->
    GESet.map (fun x -> Loc (l, Some x)) (filter_pat (p, p'))
  | Ctor_pat (kappa, arr), Ctor_pat (kappa', arr')
    when kappa = kappa' && Array.length arr = Array.length arr' ->
    let acc = ref GESet.empty in
    let i = ref 0 in
    let arr = Array.copy arr in
    let len = Array.length arr in
    while !i < len do
      let ith = filter_pat (arr.(!i), arr'.(!i)) in
      let set =
        GESet.map
          (fun x ->
            let temp = Array.copy arr in
            temp.(!i) <- x;
            Ctor_pat (kappa, temp))
          ith
      in
      acc := GESet.union !acc set;
      arr.(!i) <- arr'.(!i);
      incr i
    done;
    !acc
  | _ -> GESet.empty

let value_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_V (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_V (x, [Some y]))
  | {CL.Primitive.prim_name = "%identity"}, [Some x] -> SESet.singleton x
  | {CL.Primitive.prim_name = "%ignore"}, [Some _] ->
    SESet.singleton (Ctor (Some "()", Static [||]))
  | {CL.Primitive.prim_name = "%field0"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 0)))
  | {CL.Primitive.prim_name = "%field1"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 1)))
  | {CL.Primitive.prim_name = "%setfield0"}, [Some x; Some y] ->
    update_c (Fld (x, (None, Some 0))) (SESet.singleton y);
    SESet.singleton (Ctor (Some "()", Static [||]))
  | {CL.Primitive.prim_name = "%makemutable"}, [Some x] ->
    let i = new_memory () in
    update_loc i (SESet.singleton x);
    SESet.singleton (Ctor (None, Static [|i|]))
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_V (x, []))
  | _ -> SESet.singleton Top

let packet_prim = function
  | {CL.Primitive.prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_P (y, [Some x]))
  | {CL.Primitive.prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_P (x, [Some y]))
  | {CL.Primitive.prim_name = "%lazy_force"}, [Some x] ->
    SESet.singleton (App_P (x, []))
  | ( {
        CL.Primitive.prim_name =
          "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace";
      },
      Some x :: _ ) ->
    SESet.singleton x
  | _ -> SESet.empty

let step_sc var =
  let key = Var var in
  let reduce = function
    | (Top | Const _ | Fn _) as x -> update_g key (GESet.singleton x)
    | Ctor (kappa, Static arr) ->
      let arr' = Array.map (fun i -> Loc (i, None)) arr in
      update_g key (GESet.singleton (Ctor_pat (kappa, arr')))
    | Var x ->
      let set =
        SESet.filter
          (function
            | Prim _ | Fn (_, _) | App_V (_, None :: _) -> true
            | App_V (Prim p, l) ->
              if p.prim_arity != arg_len l then true else false
            | _ -> false)
          (Hashtbl.find sc (Var x))
      in
      update_c (Var var) set;
      if Hashtbl.mem grammar (Var x) then
        update_g key (Hashtbl.find grammar (Var x))
    | App_V (Prim p, l) ->
      if p.prim_arity = arg_len l then update_c key (value_prim (p, l))
    | App_P (Prim p, l) ->
      if p.prim_arity = arg_len l then update_c key (packet_prim (p, l))
    | App_V (Var x, []) ->
      if Hashtbl.mem grammar (Var x) then
        SESet.iter
          (function
            | Fn (None, l) ->
              let set = SESet.of_list (List.map (fun x -> Var (Val x)) l) in
              update_c (Var var) set
            | _ -> ())
          (Hashtbl.find sc (Var x))
    | App_P (Var x, []) ->
      if Hashtbl.mem grammar (Var x) then
        GESet.iter
          (function
            | Fn (None, l) ->
              let set = SESet.of_list (List.map (fun x -> Var (Packet x)) l) in
              update_c (Var var) set
            | _ -> ())
          (Hashtbl.find grammar (Var x))
    | App_V (Var x, Some (Var y) :: tl) -> ()
    | App_P (Var x, Some (Var y) :: tl) -> ()
    | Fld (Var x, (None, Some i)) -> ()
    | Fld (Var x, (Some k, Some i)) -> ()
    | Diff (Var x, p) -> ()
    | _ -> ()
  in
  ()
