open BinInt
open BinNums
open BinPos
open Bool
open CMorphisms
open CRelationClasses
open Datatypes
open Eqtype
open Finfun
open Fintype
open Seq
open Ssrbool
open Ssrfun
open Ssrnat

type __ = Obj.t

val eq_axiom_of_scheme : ('a1 -> 'a1 -> bool) -> 'a1 Equality.axiom

module FinIsCount :
 sig
  val pickle : Equality.coq_type -> Equality.sort list -> Equality.sort -> nat

  val unpickle :
    Equality.coq_type -> Equality.sort list -> nat -> Equality.sort option
 end

type 't eqTypeC = { beq : ('t -> 't -> bool); ceqP : 't Equality.axiom }

val beq : 'a1 eqTypeC -> 'a1 -> 'a1 -> bool

val ceqP : 'a1 eqTypeC -> 'a1 Equality.axiom

val ceqT_eqMixin : 'a1 eqTypeC -> 'a1 Equality.mixin_of

val ceqT_eqType : 'a1 eqTypeC -> Equality.coq_type

type 't finTypeC = { _eqC : 't eqTypeC; cenum : 't list }

val _eqC : 'a1 finTypeC -> 'a1 eqTypeC

val cenum : 'a1 finTypeC -> 'a1 list

val cfinT_choiceMixin : 'a1 finTypeC -> Equality.sort Choice.Choice.mixin_of

val cfinT_choiceType : 'a1 finTypeC -> Choice.Choice.coq_type

val cfinT_countMixin : 'a1 finTypeC -> Equality.sort Choice.Countable.mixin_of

val cfinT_countType : 'a1 finTypeC -> Choice.Countable.coq_type

val cfinT_finMixin : 'a1 finTypeC -> Finite.mixin_of

val cfinT_finType : 'a1 finTypeC -> Finite.coq_type

module FinMap :
 sig
  type ('t, 'u) map = 'u finfun_of

  val of_fun : 'a1 finTypeC -> (Finite.sort -> 'a2) -> 'a2 finfun_of

  val set : 'a1 finTypeC -> ('a1, 'a2) map -> 'a1 -> 'a2 -> ('a1, 'a2) map
 end

val reflect_inj :
  Equality.coq_type -> (Equality.sort -> 'a1) -> Equality.sort ->
  Equality.sort -> reflect -> reflect

type ('e, 'a) result =
| Ok of 'a
| Error of 'e

val is_ok : ('a1, 'a2) result -> bool

val is_okP : ('a1, 'a2) result -> reflect

module Result :
 sig
  val apply : ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2) result -> 'a3

  val bind :
    ('a2 -> ('a1, 'a3) result) -> ('a1, 'a2) result -> ('a1, 'a3) result

  val map : ('a2 -> 'a3) -> ('a1, 'a2) result -> ('a1, 'a3) result

  val default : 'a2 -> ('a1, 'a2) result -> 'a2
 end

val o2r : 'a1 -> 'a2 option -> ('a1, 'a2) result

val coq_assert : bool -> 'a1 -> ('a1, unit) result

type error =
| ErrOob
| ErrAddrUndef
| ErrAddrInvalid
| ErrStack
| ErrType
| ErrArith

type 't exec = (error, 't) result

val type_error : (error, 'a1) result

val undef_error : (error, 'a1) result

val rbindP :
  ('a1, 'a2) result -> ('a2 -> ('a1, 'a3) result) -> 'a3 -> ('a2 -> __ -> __
  -> 'a4) -> 'a4

val mapM : ('a2 -> ('a1, 'a3) result) -> 'a2 list -> ('a1, 'a3 list) result

val mapMP :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort -> ('a1,
  Equality.sort) result) -> Equality.sort list -> Equality.sort list ->
  Equality.sort -> reflect

val foldM :
  ('a2 -> 'a3 -> ('a1, 'a3) result) -> 'a3 -> 'a2 list -> ('a1, 'a3) result

val foldrM :
  ('a2 -> 'a3 -> ('a1, 'a3) result) -> 'a3 -> 'a2 list -> ('a1, 'a3) result

val fold2 :
  'a3 -> ('a1 -> 'a2 -> 'a4 -> ('a3, 'a4) result) -> 'a1 list -> 'a2 list ->
  'a4 -> ('a3, 'a4) result

val allM : ('a1 -> ('a2, unit) result) -> 'a1 list -> ('a2, unit) result

val mapM2 :
  'a3 -> ('a1 -> 'a2 -> ('a3, 'a4) result) -> 'a1 list -> 'a2 list -> ('a3,
  'a4 list) result

val fmap : ('a1 -> 'a2 -> 'a1 * 'a3) -> 'a1 -> 'a2 list -> 'a1 * 'a3 list

val fmapM :
  ('a2 -> 'a3 -> ('a1, 'a2 * 'a4) result) -> 'a2 -> 'a3 list -> ('a1,
  'a2 * 'a4 list) result

val fmapM2 :
  'a1 -> ('a2 -> 'a3 -> 'a4 -> ('a1, 'a2 * 'a5) result) -> 'a2 -> 'a3 list ->
  'a4 list -> ('a1, 'a2 * 'a5 list) result

val all2P : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> reflect

val reflect_all2_eqb :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> reflect) -> 'a1 list -> 'a1 list ->
  reflect

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val map3 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 list -> 'a2 list -> 'a3 list -> 'a4 list

val mapi_aux : (nat -> 'a1 -> 'a2) -> nat -> 'a1 list -> 'a2 list

val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

val find_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 option

val isSome : 'a1 option -> bool

val isSome_obind : ('a1 -> 'a2 option) -> 'a1 option -> reflect

val omap_dflt : 'a2 -> ('a1 -> 'a2) -> 'a1 option -> 'a2

val list_to_rev : nat -> nat list

val list_to : nat -> nat list

val conc_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val ctrans : comparison -> comparison -> comparison option

val comparison_beq : comparison -> comparison -> bool

val comparison_eq_dec : comparison -> comparison -> bool

val comparison_beqP : comparison Equality.axiom

val comparison_eqMixin : comparison Equality.mixin_of

val comparison_eqType : Equality.coq_type

val gcmp : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> comparison

val cmp_lt : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> bool

val cmp_le : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> bool

val lex :
  ('a1 -> 'a1 -> comparison) -> ('a2 -> 'a2 -> comparison) -> ('a1 * 'a2) ->
  ('a1 * 'a2) -> comparison

val cmp_min : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1

val cmp_max : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1

val bool_cmp : bool -> bool -> comparison

val subrelation_iff_flip_arrow : (__, __) iffT -> (__, __) arrow

val reflect_m : bool -> bool -> (__, __) iffT

val coq_P_leP : positive -> positive -> reflect

val coq_P_ltP : positive -> positive -> reflect

val pos_eqP : positive Equality.axiom

val pos_eqMixin : positive Equality.mixin_of

val pos_eqType : Equality.coq_type

val coq_ZleP : coq_Z -> coq_Z -> reflect

val coq_ZltP : coq_Z -> coq_Z -> reflect

val coq_ZNleP : nat -> nat -> reflect

val coq_ZNltP : nat -> nat -> reflect

val ziota_rec : coq_Z -> coq_Z -> coq_Z list

val ziota : coq_Z -> coq_Z -> coq_Z list

val pnth : 'a1 -> 'a1 list -> positive -> 'a1

val znth : 'a1 -> 'a1 list -> coq_Z -> 'a1

val zindex : Equality.coq_type -> Equality.sort -> Equality.sort list -> coq_Z

type 'tr lprod = __

type ltuple = __

val merge_tuple : __ list -> __ list -> ltuple -> ltuple -> ltuple

module Option :
 sig
 end

val obindP :
  'a1 option -> ('a1 -> 'a2 option) -> 'a2 -> ('a1 -> __ -> __ -> 'a3) -> 'a3

val oassert : bool -> unit option
