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
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val eq_axiom_of_scheme : ('a1 -> 'a1 -> bool) -> 'a1 Equality.axiom **)

let eq_axiom_of_scheme beq0 x y =
  iffP (beq0 x y) (if beq0 x y then ReflectT else ReflectF)

module FinIsCount =
 struct
  (** val pickle :
      Equality.coq_type -> Equality.sort list -> Equality.sort -> nat **)

  let pickle t enum x =
    index t x enum

  (** val unpickle :
      Equality.coq_type -> Equality.sort list -> nat -> Equality.sort option **)

  let unpickle _ enum n =
    nth None (map (fun x -> Some x) enum) n
 end

type 't eqTypeC = { beq : ('t -> 't -> bool); ceqP : 't Equality.axiom }

(** val beq : 'a1 eqTypeC -> 'a1 -> 'a1 -> bool **)

let beq eqTypeC0 =
  eqTypeC0.beq

(** val ceqP : 'a1 eqTypeC -> 'a1 Equality.axiom **)

let ceqP eqTypeC0 =
  eqTypeC0.ceqP

(** val ceqT_eqMixin : 'a1 eqTypeC -> 'a1 Equality.mixin_of **)

let ceqT_eqMixin ceqT =
  { Equality.op = ceqT.beq; Equality.mixin_of__1 = ceqT.ceqP }

(** val ceqT_eqType : 'a1 eqTypeC -> Equality.coq_type **)

let ceqT_eqType ceqT =
  ceqT_eqMixin (Obj.magic ceqT)

type 't finTypeC = { _eqC : 't eqTypeC; cenum : 't list }

(** val _eqC : 'a1 finTypeC -> 'a1 eqTypeC **)

let _eqC finTypeC0 =
  finTypeC0._eqC

(** val cenum : 'a1 finTypeC -> 'a1 list **)

let cenum finTypeC0 =
  finTypeC0.cenum

(** val cfinT_choiceMixin :
    'a1 finTypeC -> Equality.sort Choice.Choice.mixin_of **)

let cfinT_choiceMixin cfinT =
  Choice.coq_PcanChoiceMixin Choice.nat_choiceType
    (Obj.magic FinIsCount.pickle (ceqT_eqType cfinT._eqC)
      (Obj.magic cfinT).cenum)
    (Obj.magic FinIsCount.unpickle (ceqT_eqType cfinT._eqC)
      (Obj.magic cfinT).cenum)

(** val cfinT_choiceType : 'a1 finTypeC -> Choice.Choice.coq_type **)

let cfinT_choiceType cfinT =
  { Choice.Choice.base = (Equality.coq_class (ceqT_eqType cfinT._eqC));
    Choice.Choice.mixin = (cfinT_choiceMixin cfinT) }

(** val cfinT_countMixin :
    'a1 finTypeC -> Equality.sort Choice.Countable.mixin_of **)

let cfinT_countMixin cfinT =
  Choice.coq_PcanCountMixin Choice.nat_countType
    (Obj.magic FinIsCount.pickle (ceqT_eqType cfinT._eqC)
      (Obj.magic cfinT).cenum)
    (Obj.magic FinIsCount.unpickle (ceqT_eqType cfinT._eqC)
      (Obj.magic cfinT).cenum)

(** val cfinT_countType : 'a1 finTypeC -> Choice.Countable.coq_type **)

let cfinT_countType cfinT =
  { Choice.Countable.base =
    (Choice.Choice.coq_class (cfinT_choiceType cfinT));
    Choice.Countable.mixin = (cfinT_countMixin cfinT) }

(** val cfinT_finMixin : 'a1 finTypeC -> Finite.mixin_of **)

let cfinT_finMixin cfinT =
  Finite.coq_EnumMixin (cfinT_countType cfinT) (Obj.magic cfinT).cenum

(** val cfinT_finType : 'a1 finTypeC -> Finite.coq_type **)

let cfinT_finType cfinT =
  { Finite.base = (Choice.Choice.coq_class (cfinT_choiceType cfinT));
    Finite.mixin = (cfinT_finMixin cfinT) }

module FinMap =
 struct
  type ('t, 'u) map = 'u finfun_of

  (** val of_fun : 'a1 finTypeC -> (Finite.sort -> 'a2) -> 'a2 finfun_of **)

  let of_fun cfinT =
    FinfunDef.finfun (cfinT_finType cfinT)

  (** val set :
      'a1 finTypeC -> ('a1, 'a2) map -> 'a1 -> 'a2 -> ('a1, 'a2) map **)

  let set cfinT m x y =
    of_fun cfinT (fun z ->
      if eq_op (ceqT_eqType cfinT._eqC) z (Obj.magic x)
      then y
      else fun_of_fin (cfinT_finType cfinT) m z)
 end

(** val reflect_inj :
    Equality.coq_type -> (Equality.sort -> 'a1) -> Equality.sort ->
    Equality.sort -> reflect -> reflect **)

let reflect_inj t _ a b heq =
  iffP (eq_op t a b) heq

type ('e, 'a) result =
| Ok of 'a
| Error of 'e

(** val is_ok : ('a1, 'a2) result -> bool **)

let is_ok = function
| Ok _ -> true
| Error _ -> false

(** val is_okP : ('a1, 'a2) result -> reflect **)

let is_okP r =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  (match r with
   | Ok a -> _evar_0_ a
   | Error e -> _evar_0_0 e)

module Result =
 struct
  (** val apply : ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2) result -> 'a3 **)

  let apply f x = function
  | Ok y -> f y
  | Error _ -> x

  (** val bind :
      ('a2 -> ('a1, 'a3) result) -> ('a1, 'a2) result -> ('a1, 'a3) result **)

  let bind f = function
  | Ok x -> f x
  | Error s -> Error s

  (** val map : ('a2 -> 'a3) -> ('a1, 'a2) result -> ('a1, 'a3) result **)

  let map f = function
  | Ok x -> Ok (f x)
  | Error s -> Error s

  (** val default : 'a2 -> ('a1, 'a2) result -> 'a2 **)

  let default x =
    apply (fun x0 -> x0) x
 end

(** val o2r : 'a1 -> 'a2 option -> ('a1, 'a2) result **)

let o2r e = function
| Some x -> Ok x
| None -> Error e

(** val coq_assert : bool -> 'a1 -> ('a1, unit) result **)

let coq_assert b e =
  if b then Ok () else Error e

type error =
| ErrOob
| ErrAddrUndef
| ErrAddrInvalid
| ErrStack
| ErrType
| ErrArith

type 't exec = (error, 't) result

(** val type_error : (error, 'a1) result **)

let type_error =
  Error ErrType

(** val undef_error : (error, 'a1) result **)

let undef_error =
  Error ErrAddrUndef

(** val rbindP :
    ('a1, 'a2) result -> ('a2 -> ('a1, 'a3) result) -> 'a3 -> ('a2 -> __ ->
    __ -> 'a4) -> 'a4 **)

let rbindP e _ _ x =
  let _evar_0_ = fun a h -> h a __ __ in
  let _evar_0_0 = fun _ _ -> assert false (* absurd case *) in
  (match e with
   | Ok a -> _evar_0_ a x
   | Error e0 -> _evar_0_0 e0 x)

(** val mapM :
    ('a2 -> ('a1, 'a3) result) -> 'a2 list -> ('a1, 'a3 list) result **)

let rec mapM f = function
| [] -> Ok []
| x :: xs0 ->
  (match f x with
   | Ok x0 ->
     (match mapM f xs0 with
      | Ok x1 -> Ok (x0 :: x1)
      | Error s -> Error s)
   | Error s -> Error s)

(** val mapMP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort -> ('a1,
    Equality.sort) result) -> Equality.sort list -> Equality.sort list ->
    Equality.sort -> reflect **)

let mapMP _ bT f s s' y =
  let _evar_0_ = fun _ -> ReflectF in
  let _evar_0_0 = fun x s0 iHs s'0 ->
    rbindP (f x) (fun y0 ->
      match mapM f s0 with
      | Ok x0 -> Ok (y0 :: x0)
      | Error s1 -> Error s1) s'0 (fun y0 _ _ ->
      rbindP (Obj.magic mapM f s0) (fun ys -> Ok (y0 :: (Obj.magic ys))) s'0
        (fun ys _ _ ->
        let iHs' = iHs ys __ in
        let _evar_0_0 = fun _ -> ReflectT in
        let _evar_0_1 = fun _ ->
          iffP (in_mem y (mem (seq_predType bT) ys)) iHs'
        in
        if eq_op bT y0 y then _evar_0_0 __ else _evar_0_1 __))
  in
  let rec f0 l s'0 =
    match l with
    | [] -> _evar_0_ s'0
    | y0 :: l0 -> Obj.magic _evar_0_0 y0 l0 (fun s'1 _ -> f0 l0 s'1) s'0
  in f0 s s'

(** val foldM :
    ('a2 -> 'a3 -> ('a1, 'a3) result) -> 'a3 -> 'a2 list -> ('a1, 'a3) result **)

let rec foldM f acc = function
| [] -> Ok acc
| a :: la -> (match f a acc with
              | Ok x -> foldM f x la
              | Error s -> Error s)

(** val foldrM :
    ('a2 -> 'a3 -> ('a1, 'a3) result) -> 'a3 -> 'a2 list -> ('a1, 'a3) result **)

let rec foldrM f acc = function
| [] -> Ok acc
| a :: la -> (match foldrM f acc la with
              | Ok x -> f a x
              | Error s -> Error s)

(** val fold2 :
    'a3 -> ('a1 -> 'a2 -> 'a4 -> ('a3, 'a4) result) -> 'a1 list -> 'a2 list
    -> 'a4 -> ('a3, 'a4) result **)

let rec fold2 e f la lb r =
  match la with
  | [] -> (match lb with
           | [] -> Ok r
           | _ :: _ -> Error e)
  | a :: la0 ->
    (match lb with
     | [] -> Error e
     | b :: lb0 ->
       (match f a b r with
        | Ok x -> fold2 e f la0 lb0 x
        | Error s -> Error s))

(** val allM :
    ('a1 -> ('a2, unit) result) -> 'a1 list -> ('a2, unit) result **)

let allM check m =
  foldM (fun a _ -> check a) () m

(** val mapM2 :
    'a3 -> ('a1 -> 'a2 -> ('a3, 'a4) result) -> 'a1 list -> 'a2 list -> ('a3,
    'a4 list) result **)

let rec mapM2 e f la lb =
  match la with
  | [] -> (match lb with
           | [] -> Ok []
           | _ :: _ -> Error e)
  | a :: la0 ->
    (match lb with
     | [] -> Error e
     | b :: lb0 ->
       (match f a b with
        | Ok x ->
          (match mapM2 e f la0 lb0 with
           | Ok x0 -> Ok (x :: x0)
           | Error s -> Error s)
        | Error s -> Error s))

(** val fmap :
    ('a1 -> 'a2 -> 'a1 * 'a3) -> 'a1 -> 'a2 list -> 'a1 * 'a3 list **)

let rec fmap f a = function
| [] -> (a, [])
| b :: bs0 ->
  let (a0, c) = f a b in let (a1, cs) = fmap f a0 bs0 in (a1, (c :: cs))

(** val fmapM :
    ('a2 -> 'a3 -> ('a1, 'a2 * 'a4) result) -> 'a2 -> 'a3 list -> ('a1,
    'a2 * 'a4 list) result **)

let rec fmapM f a = function
| [] -> Ok (a, [])
| x :: xs0 ->
  (match f a x with
   | Ok x0 ->
     (match fmapM f (fst x0) xs0 with
      | Ok x1 -> Ok ((fst x1), ((snd x0) :: (snd x1)))
      | Error s -> Error s)
   | Error s -> Error s)

(** val fmapM2 :
    'a1 -> ('a2 -> 'a3 -> 'a4 -> ('a1, 'a2 * 'a5) result) -> 'a2 -> 'a3 list
    -> 'a4 list -> ('a1, 'a2 * 'a5 list) result **)

let rec fmapM2 e f a lb lc =
  match lb with
  | [] -> (match lc with
           | [] -> Ok (a, [])
           | _ :: _ -> Error e)
  | b :: bs ->
    (match lc with
     | [] -> Error e
     | c :: cs ->
       (match f a b c with
        | Ok x ->
          (match fmapM2 e f (fst x) bs cs with
           | Ok x0 -> Ok ((fst x0), ((snd x) :: (snd x0)))
           | Error s -> Error s)
        | Error s -> Error s))

(** val all2P : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> reflect **)

let all2P p l1 l2 =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | [] -> _evar_0_
     | a :: l -> _evar_0_0 a l)
  in
  let _evar_0_0 = fun a l3 _ __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun b l4 ->
      equivP ((&&) (p a b) (all2 p l3 l4)) (andP (p a b) (all2 p l3 l4))
    in
    (match __top_assumption_ with
     | [] -> _evar_0_0
     | a0 :: l -> _evar_0_1 a0 l)
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f l1 l2

(** val reflect_all2_eqb :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> reflect) -> 'a1 list -> 'a1 list
    -> reflect **)

let reflect_all2_eqb eqb0 _ l1 l2 =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | [] -> _evar_0_
     | a :: l -> _evar_0_0 a l)
  in
  let _evar_0_0 = fun e1 l3 _ __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun e2 l4 ->
      iffP ((&&) (eqb0 e1 e2) (all2 eqb0 l3 l4))
        (andP (eqb0 e1 e2) (all2 eqb0 l3 l4))
    in
    (match __top_assumption_ with
     | [] -> _evar_0_0
     | a :: l -> _evar_0_1 a l)
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f l1 l2

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f la lb =
  match la with
  | [] -> []
  | a :: la0 ->
    (match lb with
     | [] -> []
     | b :: lb0 -> (f a b) :: (map2 f la0 lb0))

(** val map3 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 list -> 'a2 list -> 'a3 list -> 'a4 list **)

let rec map3 f ma mb mc =
  match ma with
  | [] -> []
  | a :: ma' ->
    (match mb with
     | [] -> []
     | b :: mb' ->
       (match mc with
        | [] -> []
        | c :: mc' -> (f a b c) :: (map3 f ma' mb' mc')))

(** val mapi_aux : (nat -> 'a1 -> 'a2) -> nat -> 'a1 list -> 'a2 list **)

let rec mapi_aux f k = function
| [] -> []
| a :: l0 -> (f k a) :: (mapi_aux f (S k) l0)

(** val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapi f =
  mapi_aux f O

(** val find_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 option **)

let rec find_map f = function
| [] -> None
| a :: l0 ->
  let fa = f a in (match fa with
                   | Some _ -> fa
                   | None -> find_map f l0)

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> true
| None -> false

(** val isSome_obind : ('a1 -> 'a2 option) -> 'a1 option -> reflect **)

let isSome_obind f o =
  iff_reflect (isSome (Option.bind f o))

(** val omap_dflt : 'a2 -> ('a1 -> 'a2) -> 'a1 option -> 'a2 **)

let omap_dflt d f = function
| Some x -> f x
| None -> d

(** val list_to_rev : nat -> nat list **)

let rec list_to_rev = function
| O -> []
| S x -> x :: (list_to_rev x)

(** val list_to : nat -> nat list **)

let list_to ub =
  rev (list_to_rev ub)

(** val conc_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let conc_map f l =
  flatten (map f l)

(** val ctrans : comparison -> comparison -> comparison option **)

let ctrans c1 c2 =
  match c1 with
  | Eq -> Some c2
  | Lt -> (match c2 with
           | Eq -> Some c1
           | Lt -> Some Lt
           | Gt -> None)
  | Gt -> (match c2 with
           | Eq -> Some c1
           | Lt -> None
           | Gt -> Some Gt)

(** val comparison_beq : comparison -> comparison -> bool **)

let comparison_beq x y =
  match x with
  | Eq -> (match y with
           | Eq -> true
           | _ -> false)
  | Lt -> (match y with
           | Lt -> true
           | _ -> false)
  | Gt -> (match y with
           | Gt -> true
           | _ -> false)

(** val comparison_eq_dec : comparison -> comparison -> bool **)

let comparison_eq_dec x y =
  let b = comparison_beq x y in if b then true else false

(** val comparison_beqP : comparison Equality.axiom **)

let comparison_beqP =
  eq_axiom_of_scheme comparison_beq

(** val comparison_eqMixin : comparison Equality.mixin_of **)

let comparison_eqMixin =
  { Equality.op = comparison_beq; Equality.mixin_of__1 = comparison_beqP }

(** val comparison_eqType : Equality.coq_type **)

let comparison_eqType =
  Obj.magic comparison_eqMixin

(** val gcmp : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> comparison **)

let gcmp cmp =
  cmp

(** val cmp_lt : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> bool **)

let cmp_lt cmp x1 x2 =
  eq_op comparison_eqType (Obj.magic gcmp cmp x1 x2) (Obj.magic Lt)

(** val cmp_le : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> bool **)

let cmp_le cmp x1 x2 =
  negb (eq_op comparison_eqType (Obj.magic gcmp cmp x2 x1) (Obj.magic Lt))

(** val lex :
    ('a1 -> 'a1 -> comparison) -> ('a2 -> 'a2 -> comparison) -> ('a1 * 'a2)
    -> ('a1 * 'a2) -> comparison **)

let lex cmp1 cmp2 x y =
  match cmp1 (fst x) (fst y) with
  | Eq -> cmp2 (snd x) (snd y)
  | x0 -> x0

(** val cmp_min : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1 **)

let cmp_min cmp x y =
  if cmp_le cmp x y then x else y

(** val cmp_max : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1 **)

let cmp_max cmp x y =
  if cmp_le cmp x y then y else x

(** val bool_cmp : bool -> bool -> comparison **)

let bool_cmp b1 b2 =
  if b1 then if b2 then Eq else Gt else if b2 then Lt else Eq

(** val subrelation_iff_flip_arrow : (__, __) iffT -> (__, __) arrow **)

let subrelation_iff_flip_arrow __top_assumption_ =
  let _evar_0_ = fun _ b -> b in
  let (a, b) = __top_assumption_ in _evar_0_ a b

(** val reflect_m : bool -> bool -> (__, __) iffT **)

let reflect_m _ b2 =
  let _evar_0_ = ((fun h -> equivP b2 h), (fun h -> equivP b2 h)) in
  Obj.magic _evar_0_

(** val coq_P_leP : positive -> positive -> reflect **)

let coq_P_leP x y =
  equivP (Pos.leb x y)
    (subrelation_proper (Obj.magic __) (fun _ _ _ x0 x1 _ -> reflect_m x0 x1)
      ()
      (subrelation_respectful (Obj.magic __)
        (subrelation_respectful (Obj.magic __)
          (Obj.magic (fun _ _ -> subrelation_iff_flip_arrow)))) __ __ __
      (Pos.leb x y) (Pos.leb x y) __
      (if Pos.leb x y then ReflectT else ReflectF))

(** val coq_P_ltP : positive -> positive -> reflect **)

let coq_P_ltP x y =
  equivP (Pos.ltb x y)
    (subrelation_proper (Obj.magic __) (fun _ _ _ x0 x1 _ -> reflect_m x0 x1)
      ()
      (subrelation_respectful (Obj.magic __)
        (subrelation_respectful (Obj.magic __)
          (Obj.magic (fun _ _ -> subrelation_iff_flip_arrow)))) __ __ __
      (Pos.ltb x y) (Pos.ltb x y) __
      (if Pos.ltb x y then ReflectT else ReflectF))

(** val pos_eqP : positive Equality.axiom **)

let pos_eqP p1 p2 =
  iffP (Pos.eqb p1 p2) (if Pos.eqb p1 p2 then ReflectT else ReflectF)

(** val pos_eqMixin : positive Equality.mixin_of **)

let pos_eqMixin =
  { Equality.op = Pos.eqb; Equality.mixin_of__1 = pos_eqP }

(** val pos_eqType : Equality.coq_type **)

let pos_eqType =
  Obj.magic pos_eqMixin

(** val coq_ZleP : coq_Z -> coq_Z -> reflect **)

let coq_ZleP =
  Z.leb_spec0

(** val coq_ZltP : coq_Z -> coq_Z -> reflect **)

let coq_ZltP =
  Z.ltb_spec0

(** val coq_ZNleP : nat -> nat -> reflect **)

let coq_ZNleP x y =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if leq x y then _evar_0_ __ else _evar_0_0 __

(** val coq_ZNltP : nat -> nat -> reflect **)

let coq_ZNltP x y =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if leq (S x) y then _evar_0_ __ else _evar_0_0 __

(** val ziota_rec : coq_Z -> coq_Z -> coq_Z list **)

let rec ziota_rec first = function
| Zpos p -> first :: (ziota_rec (Z.succ first) (Z.pred (Zpos p)))
| _ -> []

(** val ziota : coq_Z -> coq_Z -> coq_Z list **)

let ziota =
  ziota_rec

(** val pnth : 'a1 -> 'a1 list -> positive -> 'a1 **)

let rec pnth dfl m p =
  match m with
  | [] -> dfl
  | a :: m0 ->
    (match p with
     | Coq_xI q -> pnth dfl m0 (Coq_xO q)
     | Coq_xO q -> pnth dfl m0 (Pos.pred_double q)
     | Coq_xH -> a)

(** val znth : 'a1 -> 'a1 list -> coq_Z -> 'a1 **)

let znth dfl m z =
  match m with
  | [] -> dfl
  | a :: m0 -> (match z with
                | Z0 -> a
                | Zpos p -> pnth dfl m0 p
                | Zneg _ -> dfl)

(** val zindex :
    Equality.coq_type -> Equality.sort -> Equality.sort list -> coq_Z **)

let zindex t t0 l =
  Z.of_nat (index t t0 l)

type 'tr lprod = __

type ltuple = __

(** val merge_tuple : __ list -> __ list -> ltuple -> ltuple -> ltuple **)

let rec merge_tuple l1 l2 =
  match l1 with
  | [] -> (fun _ p -> p)
  | _ :: l3 ->
    let rec0 = merge_tuple l3 l2 in
    (fun x x0 ->
    match l3 with
    | [] -> (match l2 with
             | [] -> x
             | _ :: _ -> Obj.magic (x, x0))
    | _ :: _ -> Obj.magic ((fst (Obj.magic x)), (rec0 (snd (Obj.magic x)) x0)))

module Option =
 struct
 end

(** val obindP :
    'a1 option -> ('a1 -> 'a2 option) -> 'a2 -> ('a1 -> __ -> __ -> 'a3) ->
    'a3 **)

let obindP oa _ _ x =
  let _evar_0_ = fun a' h -> h a' __ __ in
  let _evar_0_0 = fun _ -> assert false (* absurd case *) in
  (match oa with
   | Some a -> _evar_0_ a x
   | None -> _evar_0_0 x)

(** val oassert : bool -> unit option **)

let oassert = function
| true -> Some ()
| false -> None
