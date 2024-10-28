From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From stdpp Require Import countable.
Require Import PrimInt63 Sint63 utils gen_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type TaggedCore.

  Parameter t : Type.
  Parameter tag : t -> int.
  Parameter rtag : int -> t.

  Parameter tagI : Cancel eq rtag tag.
  Existing Instance tagI.

End TaggedCore.

Module Type TAGGED.

  Parameter t : Type.
  Parameter tag : t -> int.

  (* Equality *)
  Parameter t_eqType : eqType. (* no link between t and t_eqType... *)
  Parameter EqD : EqDecision t.
  Existing Instance EqD.
  Parameter C : Countable t.
  Existing Instance C.

  (* Map *)

  Declare Module Mt : MAP with Definition K.t := t_eqType.

End TAGGED.

Module Tagged(C:TaggedCore) <: TAGGED with Definition t := C.t
                                     with Definition tag := C.tag.

  Include C.

  Definition t_eqb (x y : t) : bool := (tag x =? tag y)%uint63.

  Lemma t_eq_axiom : Equality.axiom t_eqb.
  Proof.
    move=> x y; apply (equivP (P:= tag x = tag y)).
    + by apply Bool.iff_reflect;rewrite eqb_spec.
    split => [ | -> //].
    by apply cancel_inj.
  Qed.

  HB.instance Definition _ := hasDecEq.Build t t_eq_axiom.
  Definition t_eqType : eqType := t.

  Instance EqD : EqDecision t.
  Proof. by move=> ??; apply: reflect_dec (t_eq_axiom _ _). Defined.

  Instance C : Countable t.
  Proof.
    have int_EqD: EqDecision int.
    + move=> ??.
      by apply: reflect_dec (iff_reflect _ _ (iff_sym (eqb_spec _ _))).
    have int_C: Countable int.
    + apply (inj_countable' Uint63.to_Z of_Z).
      exact: Uint63.of_to_Z.
    by apply (inj_countable' tag rtag); apply tagI.
  Defined.

  (* Map *)

  Module CmpT <: CmpType.

    Definition t := t_eqType.
    Definition EqD : EqDecision t := _.
    Definition C : Countable t := _.

  End CmpT.

  Module Mt : MAP with Definition K.t := t_eqType := Mmake CmpT.

  Module St  := Smake CmpT.
(*   Module StP := MSetEqProperties.EqProperties St. *)
(*   Module StD := MSetDecide.WDecide St. *)

End Tagged.
