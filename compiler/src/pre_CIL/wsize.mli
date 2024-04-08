open BinNums
open Datatypes
open String0
open Eqtype
open Utils0

type wsize =
| U8
| U16
| U32
| U64
| U128
| U256

type velem =
| VE8
| VE16
| VE32
| VE64

val wsize_of_velem : velem -> wsize

type pelem =
| PE1
| PE2
| PE4
| PE8
| PE16
| PE32
| PE64
| PE128

type signedness =
| Signed
| Unsigned

val wsize_beq : wsize -> wsize -> bool

val wsize_eq_dec : wsize -> wsize -> bool

val wsize_axiom : wsize Equality.axiom

val wsize_eqMixin : wsize Equality.mixin_of

val wsize_eqType : Equality.coq_type

val wsizes : wsize list

val wsize_cmp : wsize -> wsize -> comparison

val check_size_8_64 : wsize -> (error, unit) result

val check_size_8_32 : wsize -> (error, unit) result

val check_size_16_32 : wsize -> (error, unit) result

val check_size_16_64 : wsize -> (error, unit) result

val check_size_32_64 : wsize -> (error, unit) result

val check_size_128_256 : wsize -> (error, unit) result

val string_of_wsize : wsize -> char list

val string_of_ve_sz : velem -> wsize -> char list

val pp_s : char list -> unit -> char list

val pp_sz : char list -> wsize -> unit -> char list

val pp_ve_sz : char list -> velem -> wsize -> unit -> char list

val pp_ve_sz_ve_sz :
  char list -> velem -> wsize -> velem -> wsize -> unit -> char list

val pp_sz_sz : char list -> bool -> wsize -> wsize -> unit -> char list

type reg_kind =
| Normal
| Extra

type writable =
| Constant
| Writable

type reference =
| Direct
| Pointer of writable

type v_kind =
| Const
| Stack of reference
| Reg of (reg_kind * reference)
| Inline
| Global

type safe_cond =
| X86Division of wsize * signedness
| InRange of wsize * coq_Z * coq_Z * nat
| AllInit of wsize * positive * nat

type coq_PointerData =
  wsize
  (* singleton inductive, whose constructor was Build_PointerData *)

val coq_Uptr : coq_PointerData -> wsize

type coq_MSFsize =
  wsize
  (* singleton inductive, whose constructor was Build_MSFsize *)

val msf_size : coq_MSFsize -> wsize
