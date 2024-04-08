open BinNums
open Datatypes
open String0
open Eqtype

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

(** val wsize_of_velem : velem -> wsize **)

let wsize_of_velem = function
| VE8 -> U8
| VE16 -> U16
| VE32 -> U32
| VE64 -> U64

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

(** val wsize_beq : wsize -> wsize -> bool **)

let wsize_beq x y =
  match x with
  | U8 -> (match y with
           | U8 -> true
           | _ -> false)
  | U16 -> (match y with
            | U16 -> true
            | _ -> false)
  | U32 -> (match y with
            | U32 -> true
            | _ -> false)
  | U64 -> (match y with
            | U64 -> true
            | _ -> false)
  | U128 -> (match y with
             | U128 -> true
             | _ -> false)
  | U256 -> (match y with
             | U256 -> true
             | _ -> false)

(** val wsize_eq_dec : wsize -> wsize -> bool **)

let wsize_eq_dec x y =
  let b = wsize_beq x y in if b then true else false



(** val wsizes : wsize list **)

let wsizes =
  U8 :: (U16 :: (U32 :: (U64 :: (U128 :: (U256 :: [])))))

(** val wsize_cmp : wsize -> wsize -> comparison **)

let wsize_cmp s s' =
  match s with
  | U8 -> (match s' with
           | U8 -> Eq
           | _ -> Lt)
  | U16 -> (match s' with
            | U8 -> Gt
            | U16 -> Eq
            | _ -> Lt)
  | U32 -> (match s' with
            | U8 -> Gt
            | U16 -> Gt
            | U32 -> Eq
            | _ -> Lt)
  | U64 -> (match s' with
            | U64 -> Eq
            | U128 -> Lt
            | U256 -> Lt
            | _ -> Gt)
  | U128 -> (match s' with
             | U128 -> Eq
             | U256 -> Lt
             | _ -> Gt)
  | U256 -> (match s' with
             | U256 -> Eq
             | _ -> Gt)

(** val check_size_8_64 : wsize -> (error, unit) result **)

let check_size_8_64 sz =
  if cmp_le wsize_cmp sz U64 then Ok () else Error ErrType

(** val check_size_8_32 : wsize -> (error, unit) result **)

let check_size_8_32 sz =
  if cmp_le wsize_cmp sz U32 then Ok () else Error ErrType

(** val check_size_16_32 : wsize -> (error, unit) result **)

let check_size_16_32 sz =
  if (&&) (cmp_le wsize_cmp U16 sz) (cmp_le wsize_cmp sz U32)
  then Ok ()
  else Error ErrType

(** val check_size_16_64 : wsize -> (error, unit) result **)

let check_size_16_64 sz =
  if (&&) (cmp_le wsize_cmp U16 sz) (cmp_le wsize_cmp sz U64)
  then Ok ()
  else Error ErrType

(** val check_size_32_64 : wsize -> (error, unit) result **)

let check_size_32_64 sz =
  if (&&) (cmp_le wsize_cmp U32 sz) (cmp_le wsize_cmp sz U64)
  then Ok ()
  else Error ErrType

(** val check_size_128_256 : wsize -> (error, unit) result **)

let check_size_128_256 sz =
  if (&&) (cmp_le wsize_cmp U128 sz) (cmp_le wsize_cmp sz U256)
  then Ok ()
  else Error ErrType

(** val string_of_wsize : wsize -> char list **)

let string_of_wsize = function
| U8 -> '8'::[]
| U16 -> '1'::('6'::[])
| U32 -> '3'::('2'::[])
| U64 -> '6'::('4'::[])
| U128 -> '1'::('2'::('8'::[]))
| U256 -> '2'::('5'::('6'::[]))

(** val string_of_ve_sz : velem -> wsize -> char list **)

let string_of_ve_sz ve sz =
  match ve with
  | VE8 ->
    (match sz with
     | U8 ->
       'E'::('R'::('R'::('O'::('R'::(':'::(' '::('p'::('l'::('e'::('a'::('s'::('e'::(' '::('r'::('e'::('p'::('p'::('o'::('r'::('t'::[]))))))))))))))))))))
     | U16 -> '2'::('u'::('8'::[]))
     | U32 -> '4'::('u'::('8'::[]))
     | U64 -> '8'::('u'::('8'::[]))
     | U128 -> '1'::('6'::('u'::('8'::[])))
     | U256 -> '3'::('2'::('u'::('8'::[]))))
  | VE16 ->
    (match sz with
     | U32 -> '2'::('u'::('1'::('6'::[])))
     | U64 -> '4'::('u'::('1'::('6'::[])))
     | U128 -> '8'::('u'::('1'::('6'::[])))
     | U256 -> '1'::('6'::('u'::('1'::('6'::[]))))
     | _ ->
       'E'::('R'::('R'::('O'::('R'::(':'::(' '::('p'::('l'::('e'::('a'::('s'::('e'::(' '::('r'::('e'::('p'::('p'::('o'::('r'::('t'::[])))))))))))))))))))))
  | VE32 ->
    (match sz with
     | U64 -> '2'::('u'::('3'::('2'::[])))
     | U128 -> '4'::('u'::('3'::('2'::[])))
     | U256 -> '8'::('u'::('3'::('2'::[])))
     | _ ->
       'E'::('R'::('R'::('O'::('R'::(':'::(' '::('p'::('l'::('e'::('a'::('s'::('e'::(' '::('r'::('e'::('p'::('p'::('o'::('r'::('t'::[])))))))))))))))))))))
  | VE64 ->
    (match sz with
     | U128 -> '2'::('u'::('6'::('4'::[])))
     | U256 -> '4'::('u'::('6'::('4'::[])))
     | _ ->
       'E'::('R'::('R'::('O'::('R'::(':'::(' '::('p'::('l'::('e'::('a'::('s'::('e'::(' '::('r'::('e'::('p'::('p'::('o'::('r'::('t'::[])))))))))))))))))))))

(** val pp_s : char list -> unit -> char list **)

let pp_s s _ =
  s

(** val pp_sz : char list -> wsize -> unit -> char list **)

let pp_sz s sz _ =
  append s (append ('_'::[]) (string_of_wsize sz))

(** val pp_ve_sz : char list -> velem -> wsize -> unit -> char list **)

let pp_ve_sz s ve sz _ =
  append s (append ('_'::[]) (string_of_ve_sz ve sz))

(** val pp_ve_sz_ve_sz :
    char list -> velem -> wsize -> velem -> wsize -> unit -> char list **)

let pp_ve_sz_ve_sz s ve sz ve' sz' _ =
  append s
    (append ('_'::[])
      (append (string_of_ve_sz ve sz)
        (append ('_'::[]) (string_of_ve_sz ve' sz'))))

(** val pp_sz_sz :
    char list -> bool -> wsize -> wsize -> unit -> char list **)

let pp_sz_sz s sign sz sz' _ =
  append s
    (append ('_'::('u'::[]))
      (append (string_of_wsize sz)
        (append (if sign then 's'::[] else 'u'::[]) (string_of_wsize sz'))))

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

(** val coq_Uptr : coq_PointerData -> wsize **)

let coq_Uptr pointerData =
  pointerData

type coq_MSFsize =
  wsize
  (* singleton inductive, whose constructor was Build_MSFsize *)

(** val msf_size : coq_MSFsize -> wsize **)

let msf_size mSFsize =
  mSFsize
