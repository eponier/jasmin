open Bool
open Eqtype
open Fintype
open Ssrbool

type __ = Obj.t

type 'rT finfun_on =
| Coq_finfun_nil
| Coq_finfun_cons of Finite.sort * Finite.sort list * 'rT * 'rT finfun_on

val finfun_rec :
  Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort list -> 'a1 finfun_on

val fun_of_fin_rec :
  Finite.coq_type -> Equality.sort -> Finite.sort list -> 'a1 finfun_on -> 'a1

type 'rT finfun_of =
  'rT finfun_on
  (* singleton inductive, whose constructor was FinfunOf *)

val fun_of_fin : Finite.coq_type -> 'a1 finfun_of -> Equality.sort -> 'a1

module type FinfunDefSig =
 sig
  val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of
 end

module FinfunDef :
 FinfunDefSig
