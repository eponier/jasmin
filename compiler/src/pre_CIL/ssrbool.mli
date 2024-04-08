open Bool
open Datatypes
open Ssrfun

type __ = Obj.t

val addb : bool -> bool -> bool

val isSome : 'a1 option -> bool

type 'a if_spec =
| IfSpecTrue
| IfSpecFalse

val ifPn : bool -> 'a1 -> 'a1 -> 'a1 if_spec

val iffP : bool -> reflect -> reflect

val equivP : bool -> reflect -> reflect

type alt_spec =
| AltTrue
| AltFalse

val altP : bool -> reflect -> alt_spec

val boolP : bool -> alt_spec

val andP : bool -> bool -> reflect

val and3P : bool -> bool -> bool -> reflect

type 't pred = 't -> bool

type 't predType =
  __ -> 't pred
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

val predPredType : 'a1 predType

type 't simpl_pred = ('t, bool) simpl_fun

val coq_SimplPred : 'a1 pred -> 'a1 simpl_pred

module PredOfSimpl :
 sig
  val coerce : 'a1 simpl_pred -> 'a1 pred
 end

type 't rel = 't -> 't pred

type 't mem_pred = 't pred
  (* singleton inductive, whose constructor was Mem *)

val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort

val in_mem : 'a1 -> 'a1 mem_pred -> bool

val simpl_of_mem : 'a1 mem_pred -> 'a1 simpl_pred

val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred

type 't qualifier =
  't pred_sort
  (* singleton inductive, whose constructor was Qualifier *)

val has_quality : nat -> 'a1 qualifier -> 'a1 pred_sort
