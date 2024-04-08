open Bool
open Datatypes
open Eqtype
open Ssrbool
open Ssrfun
open Ssrnat

val size : 'a1 list -> nat

val ohead : 'a1 list -> 'a1 option

val head : 'a1 -> 'a1 list -> 'a1

val behead : 'a1 list -> 'a1 list

val ncons : nat -> 'a1 -> 'a1 list -> 'a1 list

val nseq : nat -> 'a1 -> 'a1 list

val cat : 'a1 list -> 'a1 list -> 'a1 list

val rcons : 'a1 list -> 'a1 -> 'a1 list

val nth : 'a1 -> 'a1 list -> nat -> 'a1

val find : 'a1 pred -> 'a1 list -> nat

val filter : 'a1 pred -> 'a1 list -> 'a1 list

val count : 'a1 pred -> 'a1 list -> nat

val has : 'a1 pred -> 'a1 list -> bool

val all : 'a1 pred -> 'a1 list -> bool

val drop : nat -> 'a1 list -> 'a1 list

val take : nat -> 'a1 list -> 'a1 list

val catrev : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val eqseq :
  Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool

val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom

val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of

val seq_eqType : Equality.coq_type -> Equality.coq_type

val mem_seq : Equality.coq_type -> Equality.sort list -> Equality.sort -> bool

type seq_eqclass = Equality.sort list

val pred_of_seq : Equality.coq_type -> seq_eqclass -> Equality.sort pred_sort

val seq_predType : Equality.coq_type -> Equality.sort predType

val uniq : Equality.coq_type -> Equality.sort list -> bool

val index : Equality.coq_type -> Equality.sort -> Equality.sort list -> nat

type bitseq = bool list

val mask : bitseq -> 'a1 list -> 'a1 list

val rem :
  Equality.coq_type -> Equality.sort -> Equality.sort list -> Equality.sort
  list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val iota : nat -> nat -> nat list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val unzip2 : ('a1 * 'a2) list -> 'a2 list

val all2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val flatten : 'a1 list list -> 'a1 list
