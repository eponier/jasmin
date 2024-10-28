(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import ZArith gen_map utils strings.
Require Export wsize.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Syntax
 * -------------------------------------------------------------------- *)

Variant stype : Set :=
| sbool
| sint
| sarr  of positive
| sword of wsize.

(* -------------------------------------------------------------------- *)
(*
Definition string_of_stype (ty: stype) : string :=
  match ty with
  | sbool => "sbool"
  | sint => "sint"
  | sarr n => "(sarr " ++ " ?)"
  | sword sz => "(sword " ++ string_of_wsize sz ++ ")"
  end.
*)

(* -------------------------------------------------------------------- *)
Notation sword8   := (sword U8).
Notation sword16  := (sword U16).
Notation sword32  := (sword U32).
Notation sword64  := (sword U64).
Notation sword128 := (sword U128).
Notation sword256 := (sword U256).

(* -------------------------------------------------------------------- *)
Notation ty_msf := (sword msf_size).

(* -------------------------------------------------------------------- *)
Scheme Equality for stype.

Lemma stype_axiom : Equality.axiom stype_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_stype_dec_bl internal_stype_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build stype stype_axiom.


(* ** Comparison
 * -------------------------------------------------------------------- *)

Definition stype_cmp t t' :=
  match t, t' with
  | sbool   , sbool         => Eq
  | sbool   , _             => Lt

  | sint    , sbool         => Gt
  | sint    , sint          => Eq
  | sint    , _             => Lt

  | sword _ , sarr _        => Lt
  | sword w , sword w'      => wsize_cmp w w'
  | sword _ , _             => Gt

  | sarr n  , sarr n'        => Pos.compare n n'
  | sarr _  , _             => Gt
  end.

#[global]
Instance stypeO : Cmp stype_cmp.
Proof.
  constructor.
  + by case => [||n|w] [||n'|w'] //=; apply cmp_sym.
  + by move=> y x; case: x y=> [||n|w] [||n'|w'] [||n''|w''] c//=;
       try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt; apply cmp_ctrans.
  case=> [||n|w] [||n'|w'] //= h.
  + by rewrite (@cmp_eq _ _ positiveO _ _ h).
  by rewrite (@cmp_eq _ _ wsizeO _ _ h).
Qed.
(*
Module CmpStype.

  Definition t : eqType := stype.

  Definition cmp : t -> t -> comparison := stype_cmp.

  Definition cmpO : Cmp cmp := stypeO.

End CmpStype.
*)
Definition is_sbool t := t == sbool.

Lemma is_sboolP t : reflect (t=sbool) (is_sbool t).
Proof. by rewrite /is_sbool;case:eqP => ?;constructor. Qed.

Definition is_sword t := if t is sword _ then true else false.

Definition is_sarr t := if t is sarr _ then true else false.

Definition is_not_sarr t := ~~is_sarr t.

Lemma is_sarrP ty : reflect (exists n, ty = sarr n) (is_sarr ty).
Proof. by case: ty; constructor; eauto => [[]]. Qed.

Definition is_word_type (t:stype) :=
  if t is sword sz then Some sz else None.

Lemma is_word_typeP ty ws :
  is_word_type ty = Some ws -> ty = sword ws.
Proof. by case: ty => //= w [->]. Qed.

(* -------------------------------------------------------------------- *)
Definition subtype (t t': stype) :=
  match t with
  | sword w => if t' is sword w' then (w ≤ w')%CMP else false
  | _ => t == t'
  end.

Lemma subtypeE ty ty' :
  subtype ty ty' →
  match ty' with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | _         => ty = ty'
end.
Proof.
  destruct ty; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subtypeEl ty ty' :
  subtype ty ty' →
  match ty with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | _        => ty' = ty
  end.
Proof.
  destruct ty; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subtype_refl x : subtype x x.
Proof. case: x => //=. Qed.
#[global]
Hint Resolve subtype_refl : core.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|n1|sx] //.
  + by case: y => //= n2 /eqP ->.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

Lemma is_sword_subtype t1 t2 : subtype t1 t2 -> is_sword t1 = is_sword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|?|?] //;case:t2.
Qed.

