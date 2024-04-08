open Bool
open Eqtype
open Fintype
open Ssrbool

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'rT finfun_on =
| Coq_finfun_nil
| Coq_finfun_cons of Finite.sort * Finite.sort list * 'rT * 'rT finfun_on

(** val finfun_rec :
    Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort list -> 'a1
    finfun_on **)

let rec finfun_rec aT g = function
| [] -> Coq_finfun_nil
| x1 :: s1 -> Coq_finfun_cons (x1, s1, (g x1), (finfun_rec aT g s1))

(** val fun_of_fin_rec :
    Finite.coq_type -> Equality.sort -> Finite.sort list -> 'a1 finfun_on ->
    'a1 **)

let fun_of_fin_rec aT x s f_s =
  let rec fun_of_fin_rec0 x0 _ = function
  | Coq_finfun_nil -> (fun _ -> assert false (* absurd case *))
  | Coq_finfun_cons (x1, s1, y1, f_s1) ->
    (match eqP (Finite.eqType aT) x0 x1 with
     | ReflectT -> (fun _ -> y1)
     | ReflectF -> fun_of_fin_rec0 x0 s1 f_s1)
  in fun_of_fin_rec0 x s f_s __

type 'rT finfun_of =
  'rT finfun_on
  (* singleton inductive, whose constructor was FinfunOf *)

(** val fun_of_fin :
    Finite.coq_type -> 'a1 finfun_of -> Equality.sort -> 'a1 **)

let fun_of_fin aT f x =
  fun_of_fin_rec aT x
    (enum_mem aT
      (mem predPredType
        (Obj.magic PredOfSimpl.coerce (coq_SimplPred (fun _ -> true))))) f

module type FinfunDefSig =
 sig
  val finfun : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of
 end

module FinfunDef =
 struct
  (** val finfun :
      Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 finfun_of **)

  let finfun aT g =
    finfun_rec aT g
      (enum_mem aT
        (mem predPredType
          (Obj.magic PredOfSimpl.coerce (coq_SimplPred (fun _ -> true)))))

  (** val finfunE : __ **)

  let finfunE =
    __
 end
