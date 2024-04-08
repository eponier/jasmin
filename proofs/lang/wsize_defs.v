Require Import ssreflect.

(* -------------------------------------------------------------- *)
Variant wsize :=
  | U8
  | U16
  | U32
  | U64
  | U128
  | U256.

(* -------------------------------------------------------------------- *)
Variant reg_kind : Type :=
| Normal
| Extra.

Variant writable : Type := Constant | Writable.

Variant reference : Type := Direct | Pointer of writable.

Variant v_kind :=
| Const            (* global parameter  *)
| Stack of reference (* stack variable    *)
| Reg   of reg_kind * reference (* register variable *)
| Inline           (* inline variable   *)
| Global           (* global (in memory) constant *)
.
