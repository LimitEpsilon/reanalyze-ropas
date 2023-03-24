(*
 * Copyright (c) Programming Research Laboratory (ROPAS)
 *               Seoul National University, Korea
 * Copyright (c) ReScript Association
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open SetExpression
open CL.Primitive

let allocated = Hashtbl.create 10

let value_prim = function
  | {prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_v (y, [Some x]))
  | {prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_v (x, [Some y]))
  | {prim_name = "%identity" | "%opaque"}, [Some x] -> SESet.singleton (Var x)
  | {prim_name = "%ignore"}, [Some _] -> SESet.singleton (Ctor (Some "()", []))
  | {prim_name = "%field0"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 0)))
  | {prim_name = "%field1"}, [Some x] ->
    SESet.singleton (Fld (x, (None, Some 1)))
  | {prim_name = "%setfield0"}, [Some x; Some y] ->
    update_sc (Fld (x, (None, Some 0))) (SESet.singleton (Var y));
    SESet.singleton (Ctor (Some "()", []))
  | {prim_name = "%makemutable"}, [Some x] -> (
    let value = SESet.singleton (Var x) in
    match Hashtbl.find allocated x with
    | exception Not_found ->
      let i = new_memory (get_context (Var x)) in
      Hashtbl.add allocated x i;
      update_sc (Loc i) value;
      SESet.singleton (Ctor (None, [(i, None)]))
    | i ->
      update_sc (Loc i) value;
      SESet.singleton (Ctor (None, [(i, None)])))
  | {prim_name = "%lazy_force"}, [Some x] -> SESet.singleton (App_v (x, []))
  | ( {
        prim_name =
          ( "%eq" | "%noteq" | "%ltint" | "%leint" | "%gtint" | "%geint"
          | "%eqfloat" | "%noteqfloat" | "%ltfloat" | "%lefloat" | "%gtfloat"
          | "%gefloat" | "%equal" | "%notequal" | "%lessequal" | "%lessthan"
          | "%greaterequal" | "%greaterthan" | "%compare" | "%boolnot"
          | "%sequand" | "%sequor" );
      },
      _ ) ->
    SESet.of_list [Ctor (Some "true", []); Ctor (Some "false", [])]
  | ( {
        prim_name =
          "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace";
      },
      _ ) ->
    SESet.empty
  | _ -> SESet.singleton Top

let packet_prim = function
  | {prim_name = "%revapply"}, [Some x; Some y] ->
    SESet.singleton (App_p (y, [Some x]))
  | {prim_name = "%apply"}, [Some x; Some y] ->
    SESet.singleton (App_p (x, [Some y]))
  | {prim_name = "%lazy_force"}, [Some x] -> SESet.singleton (App_p (x, []))
  | ( {
        prim_name =
          "%raise" | "%reraise" | "%raise_notrace" | "%raise_with_backtrace";
      },
      Some x :: _ ) ->
    SESet.singleton (Var x)
  | {prim_name = "caml_sys_exit"}, _ -> SESet.singleton (Ctor (Some "Exit", []))
  | _ -> SESet.empty
