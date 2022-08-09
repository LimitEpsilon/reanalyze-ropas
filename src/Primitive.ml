let decode_prim = function
  | "%identity" | "%bytes_to_string" | "%bytes_of_string" -> `IDENTITY
  | "%ignore" -> `IGNORE
  | "%revapply" | "%apply" | "%loc_LOC" | "%loc_FILE" | "%loc_LINE" | "%loc_"
  | "%loc_MODULE" | "%loc_FUNCTION" ->
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
  | "%intoffloat" | "%floatofint" -> `IDENTITY
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
  | "%nativeint_of_int" | "%nativeint_to_int" -> `IDENTITY
  | "%nativeint_neg" | "%nativeint_add" | "%nativeint_sub" | "%nativeint_mul"
  | "%nativeint_div" | "%nativeint_mod" | "%nativeint_and" | "%nativeint_or"
  | "%nativeint_xor" | "%nativeint_lsl" | "%nativeint_lsr" | "%nativeint_asr" ->
    `ARITH
  | "%int32_of_int" | "%int32_to_int" -> `IDENTITY
  | "%int32_neg" | "%int32_add" | "%int32_sub" | "%int32_mul" | "%int32_div"
  | "%int32_mod" | "%int32_and" | "%int32_or" | "%int32_xor" | "%int32_lsl"
  | "%int32_lsr" | "%int32_asr" ->
    `ARITH
  | "%int64_of_int" | "%int64_to_int" -> `IDENTITY
  | "%int64_neg" | "%int64_add" | "%int64_sub" | "%int64_mul" | "%int64_div"
  | "%int64_mod" | "%int64_and" | "%int64_or" | "%int64_xor" | "%int64_lsl"
  | "%int64_lsr" | "%int64_asr" ->
    `ARITH
  | "%nativeint_of_int32" | "%nativeint_to_int32" | "%int64_of_int32"
  | "%int64_to_int32" | "%int64_of_nativeint" | "%int64_to_nativeint" ->
    `IDENTITY
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
  | "%bswap16" | "%bswap_int32" | "%bswap_int64" | "%bswap_native" | "%opaque"
    ->
    `IDENTITY
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
