(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From stdpp Require Import gmap. (* import after ssreflect, otherwise Is_true wins over is_true *)
Import ssrfun seq.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** *)


Module Type CmpType.
  Parameter t : Type.
  Parameter EqD : EqDecision t.
  Existing Instance EqD.
  Parameter C : Countable t.
  Existing Instance C.
End CmpType.

Reserved Notation "x .[ k <- v ]"
     (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").

Module Type MAP.

  Declare Module K: CmpType.

  Definition t_eqb x1 x2 :=
    if K.EqD x1 x2 then true else false.

  Lemma t_eq_axiom : Equality.axiom t_eqb.
  Proof.
    move=> x1 x2; rewrite /t_eqb.
    case: K.EqD => /=.
    + by left.
    by right.
  Qed.

  HB.instance Definition t_eqType := hasDecEq.Build K.t t_eq_axiom.

  Parameter t : Type -> Type.

  Parameter empty : forall T, t T.

  Parameter is_empty : forall T, t T -> bool.

  Parameter get : forall {T}, t T -> K.t -> option T.

  Parameter set : forall {T}, t T -> K.t -> T -> t T.

  Parameter remove :  forall {T}, t T -> K.t -> t T.

  Parameter map : forall {T1 T2}, (T1 -> T2) -> t T1 -> t T2.

  Parameter mapi : forall {T1 T2}, (K.t -> T1 -> T2) -> t T1 -> t T2.

  Parameter map2 : forall {T1 T2 T3},
    (K.t -> option T1 -> option T2 -> option T3) ->
    t T1 -> t T2 -> t T3.

  Parameter filter_map : forall {T1 T2}, (K.t -> T1 -> option T2) -> t T1 -> t T2.

  Parameter incl_def : forall {T1 T2},
     (K.t -> T1 -> bool) ->
     (K.t -> T1 -> T2 -> bool) ->
     t T1 -> t T2 -> bool.

  Parameter incl : forall {T1 T2},
     (K.t -> T1 -> T2 -> bool) ->
     t T1 -> t T2 -> bool.

  Parameter all : forall {T},
    (K.t -> T -> bool) ->
    t T -> bool.
  
  Parameter has : 
    forall {T},
      (K.t -> T -> bool) ->
      t T -> bool.

  Parameter elements : forall {T}, t T -> seq (K.t * T)%type.

  Parameter fold : forall {T A}, (K.t -> T -> A -> A) -> t T -> A -> A.

  Parameter in_codom : forall {T:eqType}, T -> t T -> bool.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).

  Parameter get0 : forall {T} x, (empty T).[x] = None.

  Parameter is_emptyP : forall {T} (m: t T), 
    reflect (forall x, m.[x] = None) (is_empty m).

  Parameter setP : forall {T} (m: t T) x y (v:T),
    m.[x <- v].[y] = if x == y then Some v else m.[y].

  Parameter setP_eq : forall {T} (m: t T) x (v:T), m.[x <- v].[x] = Some v.

  Parameter setP_neq : forall {T} (m: t T) x y (v:T), x != y -> m.[x <- v].[y] = m.[y].

  Parameter removeP : forall {T} (m: t T) x y,
    (remove m x).[y] = if x == y then None else m.[y].

  Parameter removeP_eq : forall {T} (m: t T) x,
    (remove m x).[x] = None.

  Parameter removeP_neq : forall {T} (m: t T) x y,
    x != y -> (remove m x).[y] = m.[y].

  Parameter mapP : forall {T1 T2} (f:T1 -> T2) (m:t T1) (x:K.t),
    (map f m).[x] = omap f m.[x].

  Parameter mapiP : forall {T1 T2} (f:K.t -> T1 -> T2) (m:t T1) (x:K.t),
    (mapi f m).[x] = omap (f x) m.[x].

  Parameter map2P : forall {T1 T2 T3}
    (f:K.t -> option T1 -> option T2 -> option T3) (m1:t T1) (m2:t T2) (x:K.t),
    f x None None = None ->
    (map2 f m1 m2).[x] = f x m1.[x] m2.[x].

  Parameter filter_mapP : forall {T1 T2} (f:K.t -> T1 -> option T2) (m:t T1) (x:K.t),
    (filter_map f m).[x] = obind (f x) m.[x].

  Parameter elementsP : forall {T:eqType} (kv:K.t * T) m,
    reflect (m.[kv.1] = Some kv.2) (kv \in elements m).

  Parameter elementsIn : forall T (kv:K.t * T) m,
     List.In kv (elements m) <-> m.[kv.1] = Some kv.2.

  Parameter elementsU : forall T (m:t T), uniq [seq x.1 | x <- (elements m)].

  Parameter foldP : forall {T A} (f:K.t -> T -> A -> A) m a,
    fold f m a = foldl (fun a (kv:K.t * T) => f kv.1 kv.2 a) a (elements m).

  Parameter incl_defP : forall {T1 T2} (f1:K.t -> T1 -> bool) (f:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2),
     incl_def f1 f m1 m2 <->
     (forall k,
       match get m1 k, get m2 k with
       | None, _          => true
       | Some t1, None     => f1 k t1 
       | Some t1, Some t2 => f k t1 t2
       end).

  Parameter inclP : forall {T1 T2} (f:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2),
     incl f m1 m2 <->
     (forall k,
       match get m1 k, get m2 k with
       | None, _          => true
       | Some _, None     => false
       | Some t1, Some t2 => f k t1 t2
       end).

  Parameter allP : forall {T} (f: K.t -> T -> bool) (m: t T),
    all f m <-> (forall k t, get m k = Some t -> f k t).

  Parameter hasP : forall {T} (f: K.t -> T -> bool) (m: t T),
    has f m <-> (exists k t, get m k = Some t /\ f k t).

  Parameter in_codomP : forall {T:eqType} (m:t T) v,
    in_codom v m <-> exists k, m.[k] = Some v.

End MAP.

Module Mmake (K':CmpType) <: MAP.

  Module Import K := K'.

  Definition t_eqb x1 x2 :=
    if K.EqD x1 x2 then true else false.

  Lemma t_eq_axiom : Equality.axiom t_eqb.
  Proof.
    move=> x1 x2; rewrite /t_eqb.
    case: K.EqD => /=.
    + by left.
    by right.
  Qed.

  HB.instance Definition t_eqType := hasDecEq.Build K.t t_eq_axiom.
(*
  Module Ordered := MkOrdT K.

  Module Map := FMapAVL.Make Ordered.

  Module Facts := WFacts_fun Ordered Map.
*)
  Definition t := gmap K.t.

  Definition empty T : t T := ∅. (* ∅ = empty *)

  Definition is_empty {T} (m:t T) := if map_eq_dec_empty m then true else false.

  Definition get {T} (m:t T) (k:K.t) := lookup k m.

  Definition set {T} (m:t T) (k:K.t) (v:T) := insert k v m.

  Definition remove {T} (m:t T) (k:K.t) := delete k m.

  Definition map A B (f : A -> B) (m : t A) : t B := f <$> m.

  (* We define the function with a fold, because it is not built-in.
     Ideally, we would define a built-in version on gmap. *)
  Definition mapi A B (f : K.t -> A -> B) (m : t A) : t B :=
    map_imap (fun k v => Some (f k v)) m.
(*     map_fold (fun k v acc => insert k (f k v) acc) ∅ m. *)

  (* fold is linked with elements with a fold_left, we apply rev to have
     the right order *)
  Definition elements A (m : t A) : seq (K.t * A) := reverse (map_to_list m).

  Definition fold A B (f : K.t -> A -> B -> B) (m : t A) acc : B :=
    map_fold f acc m.

  Section QUANT.
    Context (T1:Type) (T2:Type) (f: K.t -> T1 -> bool) (f2: K.t -> T1 -> T2 -> bool).

    Definition all (m : t T1) :=
      map_fold (fun k v acc => acc && f k v) true m.

    Definition has (m : t T1) :=
      map_fold (fun k v acc => acc || f k v) false m.

    Definition incl_def (m1 : t T1) (m2 : t T2) :=
      map_fold (fun k v1 acc =>
        acc &&
        match lookup k m2 with
        | None => f k v1
        | Some v2 => f2 k v1 v2
        end) true m1.

   End QUANT.

  Definition incl T1 T2 := @incl_def T1 T2 (fun _ _ => false).

  Definition in_codom {T:eqType} v (m:t T) :=
    has (fun _ v' => v == v') m.

  (* hacky implem *)
  Definition map2 {T1 T2 T3} (f:K.t -> option T1 -> option T2 -> option T3)
      (m1:t T1) (m2: t T2) : t T3 :=
    let m1' :=
      map_fold (fun k v1 acc =>
        match f k (Some v1) (lookup k m2) with
        | None => acc
        | Some v2 => insert k v2 acc
        end) ∅ m1
    in
    let m2' :=
      map_fold (fun k v2 acc =>
        match f k (lookup k m1) (Some v2) with
        | None => acc
        | Some v2 => insert k v2 acc
        end) ∅ m2
    in
    union m1' m2'.

  Definition filter_map {T1 T2} (f:K.t -> T1 -> option T2) (m:t T1) : t T2 :=
    map_imap f m.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).

  Lemma get0 T x : (empty T).[x] = None.
  Proof. done. Qed.

  Lemma is_emptyP T (m: t T): reflect (forall x, m.[x] = None) (is_empty m).
  Proof.
    rewrite /is_empty /get.
    case: map_eq_dec_empty => /=.
    + by move=> ->; left.
    move=> ?; right.
    by move=> /map_empty.
  Qed.

  Lemma setP {T} (m: t T) x y (v:T) :
    m.[x <- v].[y] = if x == y then Some v else m.[y].
  Proof.
    rewrite /set /get /=.
    case: eqP.
    + by move=> <-; rewrite lookup_insert.
    move=> ?.
    by rewrite lookup_insert_ne.
  Qed.

  Lemma setP_eq {T} (m: t T) x (v:T) : m.[x <- v].[x] = Some v.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} (m: t T) (x y:K.t) (v:T) : x != y -> m.[x <- v].[y] = m.[y].
  Proof. by rewrite setP=> /negPf ->. Qed.

  Lemma removeP {T} (m: t T) x y:
    (remove m x).[y] = if x == y then None else m.[y].
  Proof.
    rewrite /remove /get.
    case: eqP.
    + by move=> <-; rewrite lookup_delete.
    move=> ?.
    by rewrite lookup_delete_ne.
  Qed.

  Lemma removeP_eq {T} (m: t T) x: (remove m x).[x] = None.
  Proof. by rewrite removeP eq_refl. Qed.

  Lemma removeP_neq {T} (m: t T) x y: x != y -> (remove m x).[y] = m.[y].
  Proof. by rewrite removeP => /negPf ->. Qed.

  Lemma mapP {T1 T2} (f:T1 -> T2) (m:t T1) (x:K.t):
    (map f m).[x] = omap f m.[x].
  Proof. by rewrite /map /get lookup_fmap. Qed.

  Lemma mapiP {T1 T2} (f:K.t -> T1 -> T2) (m:t T1) (x:K.t):
    (mapi f m).[x] = omap (f x) m.[x].
  Proof.
    by rewrite /mapi /get map_lookup_imap.
  Qed.

  Lemma filter_mapP {T1 T2} (f:K.t -> T1 -> option T2) (m:t T1) (x:K.t):
    (filter_map f m).[x] = obind (f x) m.[x].
  Proof.
    by rewrite /filter_map /get map_lookup_imap.
  Qed.

  Lemma map2P {T1 T2 T3} (f:K.t -> option T1 -> option T2 -> option T3)
    (m1:t T1) (m2:t T2) (x:K.t):
    f x None None = None ->
    (map2 f m1 m2).[x] = f x m1.[x] m2.[x].
  Proof.
    move=> Hnone. rewrite /map2 /get.
    set g1 := fun k v1 acc => _.
    set g2 := fun k v2 acc => _.
    rewrite lookup_union.
    have [h11 h12]:
      (m1 !! x <> None -> map_fold g1 ∅ m1 !! x = f x (m1 !! x) (m2 !! x)) /\
      (m1 !! x = None -> map_fold g1 ∅ m1 !! x = None).
    + move=> {g2}.
      induction m1 using map_first_key_ind => //.
      case: IHm1 => ih1 ih2.
      split.
      + rewrite (map_fold_insert_first_key g1 _ _ _ _ H H0) {1}/g1.
        case h: (f _ _ _) => [x3|].
        + case: (x =P i).
          + move=> ?; subst x.
            by rewrite !lookup_insert.
          move=> hneq.
          by rewrite !lookup_insert_ne.
        case: (x =P i).
        + move=> ?; subst x.
          rewrite !lookup_insert h.
          by move=> _; apply ih2.
        move=> hneq.
        rewrite !lookup_insert_ne //.
      rewrite (map_fold_insert_first_key g1 _ _ _ _ H H0) {1}/g1.
      case: (x =P i).
      + move=> ?; subst x.
        by rewrite lookup_insert.
      move=> hneq.
      by case: (f _ _ _) => [x3|]; rewrite !lookup_insert_ne //.
    have [h21 h22]:
      (m2 !! x <> None -> map_fold g2 ∅ m2 !! x = f x (m1 !! x) (m2 !! x)) /\
      (m2 !! x = None -> map_fold g2 ∅ m2 !! x = None).
    + move=> {g1 h11 h12}.
      induction m2 using map_first_key_ind => //.
      case: IHm2 => ih1 ih2.
      split.
      + rewrite (map_fold_insert_first_key g2 _ _ _ _ H H0) {1}/g2.
        case h: (f _ _ _) => [x3|].
        + case: (x =P i).
          + move=> ?; subst x.
            by rewrite !lookup_insert.
          move=> hneq.
          by rewrite !lookup_insert_ne.
        case: (x =P i).
        + move=> ?; subst x.
          rewrite !lookup_insert h.
          by move=> _; apply ih2.
        move=> hneq.
        rewrite !lookup_insert_ne //.
      rewrite (map_fold_insert_first_key g2 _ _ _ _ H H0) {1}/g2.
      case: (x =P i).
      + move=> ?; subst x.
        by rewrite lookup_insert.
      move=> hneq.
      by case: (f _ _ _) => [x3|]; rewrite !lookup_insert_ne //.
    case: (m1 !! x) (m2 !! x) h11 h12 h21 h22 => [x1|] [x2|] h11 h12 h21 h22.
    + rewrite h11 // h21 //.
      by case: (f).
    + by rewrite h11 // h22 // option_union_right_id.
    + by rewrite h12 // h21 // option_union_left_id.
    by rewrite h12 // h22 //.
  Qed.

  Lemma elementsP : forall {T:eqType} (kv:K.t * T) m,
    reflect (m.[kv.1] = Some kv.2) (kv \in elements m).
  Proof.
    rewrite /elements /get; move=> T [k v] m /=.
    apply iff_reflect.
    rewrite -/(is_true _) -(rwP (xseq.InP _ _)) -elem_of_list_In elem_of_reverse.
    symmetry.
    exact: elem_of_map_to_list.
  Qed.

  Lemma elementsIn : forall T (kv:K.t * T) m,
     List.In kv (elements m) <-> m.[kv.1] = Some kv.2.
  Proof.
    rewrite /elements /get; move=> T [k v] m /=.
    rewrite -elem_of_list_In elem_of_reverse.
    exact: elem_of_map_to_list.
  Qed.

  Lemma uniq_NoDup {T:eqType} (s:seq T) :
    reflect (NoDup s) (uniq s).
  Proof.
    elim: s => [|x s ih] /=.
    + by left; constructor.
    rewrite NoDup_cons.
    case: (@idP (x \notin s)) => h.
    + apply (equivP ih).
      rewrite elem_of_list_In (rwP (xseq.InP _ _)) (rwP negP) h.
      by intuition.
    right.
    rewrite elem_of_list_In (rwP (xseq.InP _ _)) (rwP negP).
    intuition.
  Qed.

  Lemma elementsU T (m:t T): uniq [seq x.1 | x <- (elements m)].
  Proof.
    rewrite /elements.
    apply /uniq_NoDup.
    rewrite reverse_Permutation.
    exact: NoDup_fst_map_to_list.
  Qed.

  Lemma foldP : forall {T A} (f:K.t -> T -> A -> A) m a,
    fold f m a = foldl (fun a (kv:K.t * T) => f kv.1 kv.2 a) a (elements m).
  Proof.
    move=> T A f m a; rewrite /fold /elements.
    rewrite map_fold_foldr foldl_rev.
    apply foldr_ext => //.
    by move=> [??].
  Qed.

  Lemma allP {T} (f: K.t -> T -> bool) (m: t T) :
    all f m <-> (forall k t, get m k = Some t -> f k t).
  Proof.
    rewrite /all/get.
    induction m using map_first_key_ind => //.
    rewrite (map_fold_insert_first_key _ _ _ _ _ H H0) -(rwP andP) IHm.
    split.
    + move=> [h1 h2] k v.
      case: (k =P i).
      + by move=> ->; rewrite lookup_insert => -[<-].
      move=> ?; rewrite lookup_insert_ne //.
      by apply h1.
    move=> h; split.
    + move=> k v hk.
      apply h.
      by rewrite lookup_insert_ne //; congruence.
    apply h.
    by rewrite lookup_insert.
  Qed.

  Lemma hasP {T} (f: K.t -> T -> bool) (m: t T) :
    has f m <-> (exists k t, get m k = Some t /\ f k t).
  Proof.
    rewrite /has/get.
    induction m using map_first_key_ind.
    + by split=> // -[? [? [??]]].
    rewrite (map_fold_insert_first_key _ _ _ _ _ H H0) -(rwP orP) IHm.
    split.
    + case=> h.
      + move: h => [k [v [hk1 hk2]]].
        exists k, v; split=> //.
        by rewrite lookup_insert_ne //; congruence.
      exists i, x; split=> //.
      by rewrite lookup_insert.
    move=> [k [v [hk1 hk2]]].
    case: (k =P i).
    + move=> ?; subst k.
      right.
      by move: hk1; rewrite lookup_insert => -[->].
    move=> ?; left; exists k, v; split=> //.
    by move: hk1; rewrite lookup_insert_ne //.
  Qed.

  Lemma incl_defP {T1 T2} (f:K.t -> T1 -> bool) (f2:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2) :
     incl_def f f2 m1 m2 <->
     (forall k, 
       match get m1 k, get m2 k with
       | None, _          => true
       | Some t1, None     => f k t1
       | Some t1, Some t2 => f2 k t1 t2
       end).
  Proof.
    rewrite /incl_def/get.
    induction m1 using map_first_key_ind => //.
    rewrite (map_fold_insert_first_key _ _ _ _ _ H H0) -(rwP andP) {}IHm1.
    split.
    + move=> [h1 h2] k.
      case: (k =P i).
      + move=> ?; subst k.
        by rewrite lookup_insert.
      move=> ?.
      by rewrite lookup_insert_ne //.
    move=> h; split.
    + move=> k.
      case: (k =P i).
      + move=> ?; subst k.
        by rewrite H.
      move=> ?; move: (h k).
      by rewrite lookup_insert_ne //.
    move: (h i).
    by rewrite lookup_insert.
  Qed.

  Lemma inclP {T1 T2} (f:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2) :
     incl f m1 m2 <->
     (forall k,
       match get m1 k, get m2 k with
       | None, _          => true
       | Some _, None     => false
       | Some t1, Some t2 => f k t1 t2
       end).
  Proof. by apply incl_defP. Qed.

  Lemma in_codomP : forall {T:eqType} (m:t T) v,
    in_codom v m <-> exists k, m.[k] = Some v.
  Proof.
    rewrite /in_codom => T m v; rewrite hasP; split.
    + by move=> [k [t [H1 /eqP ->]]]; exists k.
    by move=> [k H];exists k, v.
  Qed.

End Mmake.
(*
Module DMmake (K:CmpType).

  Record boxed (P:K.t -> Type) := Box {
    box_t : K.t;
    box_v : P box_t;
  }.

  Definition from_boxed {P} (k:K.t) (b:option (boxed P)) : option (P k):=
    match b with
    | Some (Box k' v) =>
      match K.EqD k' k with
      | left Heq => Some (eq_rect k' P v k Heq)
      | _        => None
      end
    | _ => None
    end.

  (* we import to get eqType. Maybe we could move eqType decl to K instead? *)
  Module Import Map := Mmake K.

  Definition t (P:K.t -> Type) := Map.t (boxed P).

  Definition empty P : t P := Map.empty (boxed P).

  Definition get {P} (m:t P) (k:K.t) :=
    from_boxed k (Map.get m k).

  Definition set {P} (m:t P) (k:K.t) (v:P k) := Map.set m k (Box v).

  Definition map {P1 P2} (f:forall k:K.t, P1 k -> P2 k) (m:t P1) : t P2 :=
    Map.map (fun b => {|box_t := b.(box_t); box_v := @f b.(box_t) b.(box_v) |}) m.

  Definition map2 {P1 P2 P3}
      (f:forall k:K.t, option (P1 k) -> option (P2 k) -> option (P3 k))
      (m1:t P1) (m2:t P2): t P3 :=
    Map.map2 (fun k o1 o2 =>
        omap (@Box P3 k) (f k (from_boxed k o1) (from_boxed k o2))) m1 m2.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).

  Lemma get0 P x : (empty P).[x] = None.
  Proof. by rewrite /empty /get Map.get0. Qed.

  Lemma eq_dec_refl x: K.EqD x x = left (erefl x).
  Proof.
    case: (K.EqD x x) => // e.
    by rewrite eq_axiomK.
  Qed.

  Lemma setP {P} (m: t P) x y (v:P x) :
    m.[x <- v].[y] =
    match E.eq_dec x y with
    | left Heq => Some (eq_rect x P v y Heq)
    | _        => m.[y]
    end.
  Proof.
    rewrite /set /get /from_boxed /=.
    rewrite Map.setP;case : (x =P y) => [<- | neq];first by rewrite eq_dec_refl.
    by rewrite eq_dec_irefl.
  Qed.

  Lemma setP_eq {P} (m: t P) x (v:P x) : m.[x <- v].[x] = Some v.
  Proof. by rewrite setP eq_dec_refl. Qed.

  Lemma setP_neq {P} (m: t P) x y (v:P x) : x != y -> m.[x <- v].[y] = m.[y].
  Proof. by move=> /eqP ?;rewrite setP eq_dec_irefl. Qed.

  Lemma mapP {P1 P2} (f:forall k:K.t, P1 k -> P2 k) (m:t P1) (x:K.t):
    (map f m).[x] = omap (f x) m.[x].
  Proof.
    rewrite /map /get Map.mapP;case: Map.get => // -[z pz] /=.
    case E.eq_dec=> e //=; move:(e);rewrite -e=> {e} e.
    by rewrite eq_axiomK.
  Qed.

  Lemma map2P {P1 P2 P3} (f:forall k:K.t, option (P1 k) -> option (P2 k) -> option (P3 k))
    (m1:t P1)(m2:t P2) (x:K.t):
    f x None None = None ->
    (map2 f m1 m2).[x] = (f x) m1.[x] m2.[x].
  Proof.
    move=> Hf;rewrite /get /map2 Map.map2P /=;last by rewrite Hf.
    by case: (f x)=> //= ?;rewrite eq_dec_refl.
  Qed.

End DMmake. *)

(* --------------------------------------------------------------------------
 ** Map of positive
 * -------------------------------------------------------------------------- *)

Require Import ZArith.

Module CmpPos <: CmpType.

  Definition t := positive.
  Definition EqD : EqDecision t := _.
  Definition C : Countable t := _.

End CmpPos.

Module Mp := Mmake CmpPos.

(* --------------------------------------------------------------------------
 ** Map of Z
 * -------------------------------------------------------------------------- *)

Module CmpZ <: CmpType.

  Definition t := Z.
  Definition EqD : EqDecision t := _.
  Definition C : Countable t := _.

End CmpZ.

Module Mz := Mmake CmpZ.

(* --------------------------------------------------------------------------
 ** Finite Set
 * -------------------------------------------------------------------------- *)

Module Smake (Import K:CmpType).
  Definition t := gset K.t.
End Smake.

Module PosSet.
  Module Sp  := Smake CmpPos.
End PosSet.
