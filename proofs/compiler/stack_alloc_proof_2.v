(* This file is the second part of [stack_alloc_proof.v] that was split to
   ease the development process. The split is not unnatural, since it
   corresponds to the end of a section.

   Though, it remains to decide whether we will fusion the two
   files back once the main proof effort has been completed.
*)

(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import psem psem_facts compiler_util constant_prop_proof.
Require Export psem stack_alloc stack_alloc_proof.
Require Import byteset.
Require Import Psatz.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
Local Open Scope Z_scope.

Import Region.

(* When the boolean is set to false, some checks are disable. On the Coq side,
   we want to perform all the checks, so we set it to true.
*)
Notation alloc_fd   := (alloc_fd true).
Notation alloc_i    := (alloc_i true).
Notation alloc_prog := (alloc_prog true).

Section INIT.

Variable global_data : seq u8.
Variable global_alloc : seq (var * wsize * Z).

Let glob_size := Z.of_nat (size global_data).

Variable rip : u64.
Hypothesis no_overflow_glob_size : no_overflow rip glob_size.

Variable mglob : Mvar.t (Z * wsize).

Hypothesis hmap : init_map (Z.of_nat (size global_data)) global_alloc = ok mglob.

Lemma init_mapP : forall x1 ofs1 ws1,
  Mvar.get mglob x1 = Some (ofs1, ws1) -> [/\
    ofs1 mod wsize_size ws1 = 0,
    0 <= ofs1 /\ ofs1 + size_slot x1 <= glob_size &
    (forall x2 ofs2 ws2,
      Mvar.get mglob x2 = Some (ofs2, ws2) -> x1 <> x2 ->
      ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1)].
Proof.
  move: hmap; rewrite /init_map.
  t_xrbindP=> -[mglob' size] hfold /=.
  case: ZleP => [hle|//] [?] x1 ofs1 ws1 hget; subst mglob'.
  have: [/\ ofs1 mod wsize_size ws1 = 0,
    0 <= ofs1 /\ ofs1 + size_slot x1 <= size &
    ∀ x2 ofs2 ws2,
      Mvar.get mglob x2 = Some (ofs2, ws2) -> x1 ≠ x2 ->
      ofs1 + size_slot x1 <= ofs2 ∨ ofs2 + size_slot x2 <= ofs1];
  last first.
  + by move=> [h1 h2 h3]; split=> //; lia.
  move: hfold x1 ofs1 ws1 hget.
  have: 0 <= (Mvar.empty (Z * wsize), 0).2 /\
    forall x1 ofs1 ws1,
    Mvar.get (Mvar.empty (Z * wsize), 0).1 x1 = Some (ofs1, ws1) -> [/\
    ofs1 mod wsize_size ws1 = 0,
    0 <= ofs1 /\ ofs1 + size_slot x1 <= (Mvar.empty (Z * wsize), 0).2 &
      (forall x2 ofs2 ws2,
        Mvar.get (Mvar.empty (Z * wsize), 0).1 x2 = Some (ofs2, ws2) -> x1 <> x2 ->
        ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1)].
  + done.
  elim: global_alloc (Mvar.empty _, 0).
  + by move=> [mglob0 size0] [_ hbase2] /= [<- <-].
  move=> [[x wsx] ofsx] l ih [mglob0 size0] /= [hbase1 hbase2].
  t_xrbindP=> -[mglob1 size1].
  case: ZleP => [h1|//].
  case: eqP => [h2|//].
  move=> [<- <-].
  apply ih.
  split=> /=.
  + by have := size_slot_gt0 x; lia.
  move=> x1 ofs1 ws1.
  rewrite Mvar.setP.
  case: eqP => [|_].
  + move=> <- [<- <-].
    split.
    + by rewrite -Zland_mod.
    + by lia.
    move=> x2 ofs2 ws2.
    rewrite Mvar.setP.
    case: eqP => [//|_].
    by move=> /hbase2 [_ ? _] _; right; lia.
  move=> /hbase2 [???]; split=> //.
  + by have := size_slot_gt0 x; lia.
  move=> x2 ofs2 ws2.
  rewrite Mvar.setP.
  case: eqP; last by eauto.
  by move=> <- [<- _] _; left; lia.
Qed.

Lemma init_map_align x1 ofs1 ws1 :
  Mvar.get mglob x1 = Some (ofs1, ws1) -> ofs1 mod wsize_size ws1 = 0.
Proof. by move=> /init_mapP [? _ _]. Qed.

Lemma init_map_bounded x1 ofs1 ws1 :
  Mvar.get mglob x1 = Some (ofs1, ws1) ->
  0 <= ofs1 /\ ofs1 + size_slot x1 <= glob_size.
Proof. by move=> /init_mapP [_ ? _]. Qed.

Lemma init_map_disjoint x1 ofs1 ws1 :
  Mvar.get mglob x1 = Some (ofs1, ws1) ->
  forall x2 ofs2 ws2,
    Mvar.get mglob x2 = Some (ofs2, ws2) -> x1 <> x2 ->
    ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1.
Proof. by move=> /init_mapP [_ _ ?]. Qed.


Variable (P : uprog) (ev: extra_val_t (progT := progUnit)).
Notation gd := (p_globs P).

Hypothesis hglobs : check_globs gd mglob global_data.

Lemma check_globP gd :
  check_glob mglob global_data gd ->
  exists ofs ws,
    Mvar.get mglob gd.1 = Some (ofs, ws) /\
    forall k w,
      get_val_byte (gv2val gd.2) k = ok w ->
      nth 0%R global_data (Z.to_nat (ofs + k)) = w.
Proof.
  rewrite /check_glob.
  case heq: Mvar.get => [[ofs ws]|//].
  move=> h; eexists _, _; (split; first by reflexivity); move: h.
  move /init_map_bounded in heq.
  case: gd.2.
  + move=> ws' w /andP [] /leP; rewrite size_drop => hle /eqP hw.
    move=> k u /=.
    case: andP => //; rewrite !zify => hbound [<-].
    rewrite Z2Nat.inj_add; try lia.
    rewrite -nth_drop -(@nth_take (Z.to_nat (wsize_size ws')));
      last by apply /ltP; apply Z2Nat.inj_lt; lia.
    rewrite /LE.wread8.
    f_equal.
    apply (LE.decode_inj (sz:=ws')).
    + rewrite size_take size_drop LE.size_encode.
      by case: ltP; lia.
    + rewrite size_take size_drop.
      by case: ltP; lia.
    by rewrite -hw LE.decodeK.
  move=> len a /andP [] /leP; rewrite size_drop => hle /allP hread.
  move=> k w /dup[] /get_val_byte_bound /= hbound hw.
  apply /eqP; rewrite Z2Nat.inj_add; try lia.
  move: (hread (Z.to_nat k)).
  rewrite Z2Nat.id; last by lia.
  rewrite hw nth_drop.
  apply.
  rewrite mem_iota; apply /andP; split; first by apply /leP; lia.
  by apply /ltP; apply Z2Nat.inj_lt; lia.
Qed.

(* TODO: surely we can avoid doing an induction (use instead standard lemma on all) *)
Lemma check_globsP g gv :
  get_global_value gd g = Some gv ->
  exists ofs ws,
    Mvar.get mglob g = Some (ofs, ws) /\
    forall k w,
      get_val_byte (gv2val gv) k = ok w ->
      nth 0%R global_data (Z.to_nat (ofs + k)) = w.
Proof.
  move: hglobs; rewrite /check_globs.
  elim: gd => // -[g' gv'] gd ih /= /andP [/check_globP h1 /ih h2].
  case: eqP => [|//].
  by move=> -> [<-].
Qed.

Section LOCAL.

(*
Variable (P : uprog) (ev: extra_val_t (progT := progUnit)).
Notation gd := (p_globs P).
*)

(* Variable rip : u64.

Variable mglob : Mvar.t (Z * wsize).
Variable gsize : Z.

Hypothesis gsize_ge0 : 0 <= gsize.
Hypothesis mglob_align : forall x ofs ws, Mvar.get mglob x = Some (ofs, ws) ->
  ofs mod wsize_size ws = 0.
Hypothesis gsize_bound : forall x ofs ws, Mvar.get mglob x = Some (ofs, ws) ->
  0 <= ofs /\ ofs + size_slot x <= gsize.
Hypothesis gsize_no_overflow : wunsigned rip + gsize <= wbase Uptr.
(* TODO: do we need disjoint global regions too ? *)
*)

Variable fn : funname.
Variable sao : stk_alloc_oracle_t.
Variable stack : Mvar.t (Z * wsize).

Hypothesis hlayout : init_stack_layout fn mglob sao = ok stack.

Lemma init_stack_layoutP :
  0 <= sao.(sao_size) /\
  forall x1 ofs1 ws1,
    Mvar.get stack x1 = Some (ofs1, ws1) -> [/\
      (ws1 <= sao.(sao_align))%CMP,
      ofs1 mod wsize_size ws1 = 0,
      0 <= ofs1 /\ ofs1 + size_slot x1 <= sao.(sao_size),
      (forall x2 ofs2 ws2,
        Mvar.get stack x2 = Some (ofs2, ws2) -> x1 <> x2 ->
        ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1) &
      Mvar.get mglob x1 = None].
Proof.
  move: hlayout; rewrite /init_stack_layout.
  t_xrbindP=> -[stack' size] hfold.
  rewrite Zcmp_le.
  case: ZleP => [hle|//] [?]; subst stack'.
  have: 0 <= size /\
    forall x1 ofs1 ws1,
    Mvar.get stack x1 = Some (ofs1, ws1) -> [/\
      (ws1 ≤ sao_align sao)%CMP, ofs1 mod wsize_size ws1 = 0,
      0 <= ofs1 /\ ofs1 + size_slot x1 <= size,
      (forall x2 ofs2 ws2,
        Mvar.get stack x2 = Some (ofs2, ws2) -> x1 <> x2 ->
        ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1) &
      Mvar.get mglob x1 = None];
  last first.
  + move=> [h1 h2]; split; first by lia.
    by move=> x1 ofs1 ws1 /h2 [?????]; split=> //; lia.
  move: hfold.
  have: 0 <= (Mvar.empty (Z * wsize), 0).2 /\
    forall x1 ofs1 ws1,
    Mvar.get (Mvar.empty (Z * wsize), 0).1 x1 = Some (ofs1, ws1) -> [/\
      (ws1 <= sao.(sao_align))%CMP,
      ofs1 mod wsize_size ws1 = 0,
      0 <= ofs1 /\ ofs1 + size_slot x1 <= (Mvar.empty (Z * wsize), 0).2,
      (forall x2 ofs2 ws2,
        Mvar.get (Mvar.empty (Z * wsize), 0).1 x2 = Some (ofs2, ws2) -> x1 <> x2 ->
        ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1) &
      Mvar.get mglob x1 = None].
  + done.
  elim: sao.(sao_slots) (Mvar.empty _, 0).
  + by move=> [stack0 size0] /= hbase [<- <-].
  move=> [[x wsx] ofsx] l ih [stack0 size0] /= [hbase1 hbase2].
  t_xrbindP=> -[stack1 size1].
  case: Mvar.get => //.
  case heq: Mvar.get => //.
  case: ifP => [|//]; rewrite Zcmp_le => /ZleP h1.
  case: ifP => [h2|//].
  case: eqP => [h3|//].
  move=> [<- <-].
  apply ih.
  split=> /=.
  + by have := size_of_gt0 x.(vtype); lia.
  move=> x1 ofs1 ws1.
  rewrite Mvar.setP.
  case: eqP => [|_].
  + move=> <- [<- <-].
    split=> //.
    + by rewrite -Zland_mod.
    + by lia.
    move=> x2 ofs2 ws2.
    rewrite Mvar.setP.
    case: eqP => [|_]; first by congruence.
    by move=> /hbase2 [_ _ ? _]; lia.
  move=> /hbase2 /= [????]; split=> //.
  + by have := size_of_gt0 x.(vtype); lia.
  move=> x2 ofs2 ws2.
  rewrite Mvar.setP.
  case: eqP; last by eauto.
  by move=> <- [<- _]; lia.
Qed.

Lemma init_stack_layout_size_ge0 : 0 <= sao.(sao_size).
Proof. by have [? _] := init_stack_layoutP. Qed.

Lemma init_stack_layout_stack_align x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) -> (ws1 <= sao.(sao_align))%CMP.
Proof. by have [_ h] := init_stack_layoutP => /h [? _ _ _ _]. Qed.

Lemma init_stack_layout_align x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) -> ofs1 mod wsize_size ws1 = 0.
Proof. by have [_ h] := init_stack_layoutP => /h [_ ? _ _ _]. Qed.

Lemma init_stack_layout_bounded x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) ->
  0 <= ofs1 /\ ofs1 + size_slot x1 <= sao.(sao_size).
Proof. by have [_ h] := init_stack_layoutP => /h [_ _ ? _ _]. Qed.

Lemma init_stack_layout_disjoint x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) ->
  forall x2 ofs2 ws2,
    Mvar.get stack x2 = Some (ofs2, ws2) -> x1 <> x2 ->
    ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1.
Proof. by have [_ h] := init_stack_layoutP => /h [_ _ _ ? _]. Qed.

Lemma init_stack_layout_not_glob x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) -> Mvar.get mglob x1 = None.
Proof. by have [_ h] := init_stack_layoutP => /h [_ _ _ _ ?]. Qed.

(*



map2

(* Section INIT_STACK. *)


Variables vrip' vrsp' : var.

Variables rsp : u64.


Hypothesis disjoint_globals_locals :
  disjoint_zrange rip gsize rsp size.
*)

Record wf_Slots (Slots : Sv.t) Addr (Writable:slot-> bool) Align := {
  wfsl_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s);
  wfsl_disjoint : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
    Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2);
  wfsl_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s);
  wfsl_not_glob : forall s, Sv.In s Slots -> Writable s ->
    0 < glob_size -> disjoint_zrange rip glob_size (Addr s) (size_slot s)
}.

Variable rsp : u64.
Hypothesis no_overflow_size : no_overflow rsp sao.(sao_size).
Hypothesis disjoint_zrange_globals_locals :
  0 < glob_size -> 0 < sao.(sao_size) ->
  disjoint_zrange rip glob_size rsp sao.(sao_size).
Hypothesis rip_align : is_align rip U256.
  (* could be formulated [forall ws, is_align rip ws] (cf. extend_mem) *)
Hypothesis rsp_align : is_align rsp sao.(sao_align).

Definition Slots_slots (m : Mvar.t (Z * wsize)) :=
  SvP.MP.of_list (map fst (Mvar.elements m)).

Lemma in_Slots_slots m s :
  Sv.In s (Slots_slots m) <-> Mvar.get m s <> None.
Proof.
  rewrite /Slots_slots; split.
  + move=> /SvP.MP.of_list_1 /SetoidList.InA_alt.
    move=> [_ [<- /InP /mapP]].
    move=> [[s' ?]] /Mvar.elementsP /= ??; subst s'.
    by congruence.
  move=> hget.
  apply SvP.MP.of_list_1; apply SetoidList.InA_alt.
  exists s; split=> //.
  apply /InP; apply /mapP.
  case heq: (Mvar.get m s) => [ofs_align|//].
  exists (s, ofs_align) => //.
  by apply /Mvar.elementsP.
Qed.

Definition Offset_slots (m : Mvar.t (Z * wsize)) s :=
  match Mvar.get m s with
  | Some (ofs, _) => ofs
  | _ => 0
  end.

Definition Align_slots (m : Mvar.t (Z * wsize)) s :=
  match Mvar.get m s with
  | Some (_, ws) => ws
  | _ => U8
  end.

Definition Slots_globals := Slots_slots mglob.
Definition Addr_globals s := (rip + wrepr _ (Offset_slots mglob s))%R.
Definition Writable_globals (s:slot) := false.
Definition Align_globals := Align_slots mglob.

Definition Slots_locals := Slots_slots stack.
Definition Addr_locals s := (rsp + wrepr _ (Offset_slots stack s))%R.
Definition Writable_locals (s:slot) := true.
Definition Align_locals := Align_slots stack.

Variable params : seq var_i.
Variables vargs1 vargs2 : seq value.
Variable m1 m2 : mem.
(* TODO: swap glob_size and rip as section variables in stack_alloc_proof? *)
Hypothesis Hargs : Forall3 (wf_arg glob_size rip m1 m2) sao.(sao_params) vargs1 vargs2.
Hypothesis Hdisj : disjoint_values sao.(sao_params) vargs1 vargs2.
Hypothesis Hsub : Forall3 (fun opi (x:var_i) v => opi <> None -> subtype x.(vtype) (type_of_val v)) sao.(sao_params) params vargs1.
(* subtype or directly size_slot x <= size_val v ?? *)
(* could we have the equality if we consider v after the truncate_val ?? *)

(* [param_info] is registered as [eqType], so that we can use all operators of
   the [seq] library on sequences containing [param_info]s.
   Is it the right place to perform this registration?
*)
Definition param_info_beq pi1 pi2 :=
  [&& pi1.(pp_ptr) == pi2.(pp_ptr),
      pi1.(pp_writable) == pi2.(pp_writable) &
      pi1.(pp_align) == pi2.(pp_align)].

Lemma param_info_axiom : Equality.axiom param_info_beq.
Proof.
  move=> [ptr1 w1 al1] [ptr2 w2 al2].
  by apply:(iffP and3P) => /= [[/eqP -> /eqP -> /eqP ->] | [-> -> ->]].
Qed.

Definition param_info_eqMixin := Equality.Mixin param_info_axiom.
Canonical  param_info_eqType  := EqType param_info param_info_eqMixin.

(* We would have liked to do the same for values, but this is not trivial at all
   for arrays, thus we still have non-eqType in our sequences, which is painful.
*)

Definition param_tuples :=
  let s := zip params (zip sao.(sao_params) (zip vargs1 vargs2)) in
  pmap (fun '(x, (opi, (v1, v2))) =>
    omap (fun pi => (x.(v_var), (pi, (v1, v2)))) opi) s.

Definition Slots_params := SvP.MP.of_list (map fst param_tuples).

Definition get_pi s := assoc param_tuples s.

Definition Addr_params s :=
  match get_pi s with
  | Some (_, (_, Vword Uptr w)) => w
  | _                           => 0%R
  end.

Definition Writable_params s :=
  match get_pi s with
  | Some (pi, _) => pi.(pp_writable)
  | None         => false
  end.

Definition Align_params s :=
  match get_pi s with
  | Some (pi, _) => pi.(pp_align)
  | None         => U8
  end.

(* Slots : glob + stack + params *)
Definition Slots :=
  Sv.union Slots_globals (Sv.union Slots_locals Slots_params).

Lemma in_Slots s :
  Sv.In s Slots <->
    Sv.In s Slots_globals \/ Sv.In s Slots_locals \/ Sv.In s Slots_params.
Proof. by rewrite /Slots; rewrite !Sv.union_spec. Qed.

Definition pick_slot A (f_globals f_locals f_params : slot -> A) s :=
  if Sv.mem s Slots_globals then f_globals s
  else if Sv.mem s Slots_locals then f_locals s
  else f_params s.

Definition Addr := pick_slot Addr_globals Addr_locals Addr_params.
Definition Writable := pick_slot Writable_globals Writable_locals Writable_params.
Definition Align := pick_slot Align_globals Align_locals Align_params.

Lemma wunsigned_Addr_globals s ofs ws :
  Mvar.get mglob s = Some (ofs, ws) ->
  wunsigned (Addr_globals s) = wunsigned rip + ofs.
Proof.
  move=> hget.
  rewrite /Addr_globals /Offset_slots hget.
  rewrite wunsigned_add //.
  have hbound := init_map_bounded hget.
  move: no_overflow_glob_size; rewrite /no_overflow zify => hover.
  have := ge0_wunsigned rip.
  have := size_slot_gt0 s.
  by lia.
Qed.

Lemma zbetween_Addr_globals s :
  Sv.In s Slots_globals ->
  zbetween rip glob_size (Addr_globals s) (size_slot s).
Proof.
  move=> /in_Slots_slots.
  case heq: Mvar.get => [[ofs ws]|//] _.
  rewrite /zbetween !zify (wunsigned_Addr_globals heq).
  have hbound := init_map_bounded heq.
  by lia.
Qed.

Lemma wunsigned_Addr_locals s ofs ws :
  Mvar.get stack s = Some (ofs, ws) ->
  wunsigned (Addr_locals s) = wunsigned rsp + ofs.
Proof.
  move=> hget.
  rewrite /Addr_locals /Offset_slots hget.
  rewrite wunsigned_add //.
  have hbound := init_stack_layout_bounded hget.
  move: no_overflow_size; rewrite /no_overflow zify => hover.
  have := ge0_wunsigned rsp.
  have := size_slot_gt0 s.
  by lia.
Qed.

Lemma zbetween_Addr_locals s :
  Sv.In s Slots_locals ->
  zbetween rsp sao.(sao_size) (Addr_locals s) (size_slot s).
Proof.
  move=> /in_Slots_slots.
  case heq: Mvar.get => [[ofs ws]|//] _.
  rewrite /zbetween !zify (wunsigned_Addr_locals heq).
  have hbound := init_stack_layout_bounded heq.
  by lia.
Qed.

(* TODO: move *)
Lemma disjointP s1 s2' :
  reflect (forall x, Sv.In x s1 -> Sv.In x s2' -> False) (disjoint s1 s2').
Proof.
  case: (@idP (disjoint s1 s2')) => hdisj; constructor.
  + move=> x h1 h2.
    move: hdisj; rewrite /disjoint => /Sv.is_empty_spec /(_ x) /Sv.inter_spec.
    by apply.
  move=> h; apply hdisj.
  rewrite /disjoint.
  by apply Sv.is_empty_spec => x /Sv.inter_spec []; apply h.
Qed.

Lemma disjoint_globals_locals : disjoint Slots_globals Slots_locals.
Proof.
  apply /disjointP => s /in_Slots_slots ? /in_Slots_slots.
  case heq: Mvar.get => [[ofs ws]|//].
  by move /init_stack_layout_not_glob in heq.
Qed.

Lemma pick_slot_globals s :
  Sv.In s Slots_globals ->
  forall A (f_globals f_locals f_params : slot -> A),
  pick_slot f_globals f_locals f_params s = f_globals s.
Proof. by rewrite /pick_slot => /Sv_memP ->. Qed.

Lemma pick_slot_locals s :
  Sv.In s Slots_locals ->
  forall A (f_globals f_locals f_params : slot -> A),
  pick_slot f_globals f_locals f_params s = f_locals s.
Proof.
  rewrite /pick_slot.
  case: Sv_memP => [|_].
  + by move /disjointP : disjoint_globals_locals => h /h.
  by move=> /Sv_memP ->.
Qed.


Variable vripn : Ident.ident.
Let vrip0 := {| vtype := sptr; vname := vripn |}.
Variable vrspn : Ident.ident.
Let vrsp0 := {| vtype := sptr; vname := vrspn |}.
Variable locals1 : Mvar.t ptr_kind.
Variable rmap1 : region_map.
Variable vnew1 : Sv.t.
Hypothesis hlocal_map : init_local_map vrip0 vrsp0 fn mglob stack sao = ok (locals1, rmap1, vnew1).
(* Variable params : seq var_i. *)
Variable vnew2 : Sv.t.
Variable locals2 : Mvar.t ptr_kind.
Variable rmap2 : region_map.
Variable alloc_params : seq (option sub_region * var_i).
Hypothesis hparams : init_params mglob stack vnew1 locals1 rmap1 sao.(sao_params) params = ok (vnew2, locals2, rmap2, alloc_params).

Lemma uniq_param_tuples : uniq (map fst param_tuples).
Proof.
  have: uniq (map fst param_tuples) /\
    forall x, x \in map fst param_tuples -> Mvar.get locals1 x = None;
  last by move=> [].
  rewrite /param_tuples.
  move: hparams; rewrite /init_params.
  elim: sao.(sao_params) params vargs1 vargs2 vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params;
    first by move=> [|??] [|??] [|??].
  move=> opi sao_params ih [|x params'] [|varg1 vargs1'] [|varg2 vargs2'] //.
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' /=.
  t_xrbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param'] _ _.
  case heq: Mvar.get => //.
  case: opi => [pi|]; last first.
  + by move=> [<- <- <- <-] [[[??]?]?] /ih -/(_ vargs1' vargs2') [ih1 ih2] _ _.
  t_xrbindP=> _ _ _ _ _ _.
  case: Mvar.get => //.
  case: Mvar.get => //.
  case: Mvar.get => //.
  move=> [_ ? _ _]; subst locals1'.
  move=> [[[_ _] _] _] /ih -/(_ vargs1' vargs2') [ih1 ih2] _ _.
  split=> /=.
  + apply /andP; split=> //.
    apply /negP => /ih2.
    by rewrite Mvar.setP_eq.
  move=> y; rewrite in_cons => /orP.
  case.
  + by move=> /eqP ->.
  move=> /ih2.
  by rewrite Mvar.setP; case: eqP.
Qed.

Lemma in_Slots_params s :
  Sv.In s Slots_params <-> get_pi s <> None.
Proof.
  rewrite /Slots_params /get_pi SvP.MP.of_list_1 SetoidList.InA_alt.
  split.
  + move=> [] _ [<-] /InP /in_map [[x [opi v]] hin ->].
    by have -> := mem_uniq_assoc hin uniq_param_tuples.
  case heq: assoc => [[pi [v1 v2]]|//] _.
  exists s; split=> //.
  apply /InP; apply /in_map.
  exists (s, (pi, (v1, v2))) => //.
  by apply assoc_mem'.
Qed.

Lemma init_params_not_glob_nor_stack s pi :
  get_pi s = Some pi ->
  Mvar.get mglob s = None /\ Mvar.get stack s = None.
Proof.
  rewrite /get_pi /param_tuples.
  move: hparams; rewrite /init_params.
  elim: params sao.(sao_params) vargs1 vargs2 vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params;
    first by move=> [|??] [|??] [|??].
  move=> x params' ih [|opi2 sao_params] [|varg1 vargs1'] [|varg2 vargs2'] //.
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' /=.
  t_xrbindP=> -[[[??]?]?] _ _.
  case: Mvar.get => //.
  case: opi2 => [pi2|]; last first.
  + by move=> [<- <- <- <-] [[[??]?]?] /ih{ih}ih _ _; apply ih.
  t_xrbindP=> _ _ _ _ _ _.
  case: Mvar.get => //.
  case heq1: Mvar.get => //.
  case heq2: Mvar.get => //.
  move=> _ [[[_ _] _] _] /ih{ih}ih _ _ /=.
  case: eqP => [-> //|_].
  by apply ih.
Qed.

(* TODO: move? *)
Lemma Forall2_size A B (R : A -> B -> Prop) l1 l2 :
  List.Forall2 R l1 l2 -> size l1 = size l2.
Proof. by move=> h; elim: h => // a b l1' l2' _ _ /= ->. Qed.

(*
Lemma Forall3_impl A B C (R1 R2 : A -> B -> C -> Prop) :
  (forall a b c, R1 a b c -> R2 a b c) ->
  forall l1 l2 l3,
  Forall3 R1 l1 l2 l3 ->
  Forall3 R2 l1 l2 l3.
Proof.
  move=> himpl l1 l2 l3 hforall.
  elim: hforall; eauto using Forall3.
Qed.
*)
Lemma Forall3_impl_in A B C (R1 R2 : A -> B -> C -> Prop) la lb lc :
  (forall a b c, List.In a la -> List.In b lb -> List.In c lc -> R1 a b c -> R2 a b c) ->
  Forall3 R1 la lb lc ->
  Forall3 R2 la lb lc.
Proof.
  move=> h1 h2.
  elim: {la lb lc} h2 h1.
  + by constructor.
  move=> a b c la lb lc hr1 _ ih himpl.
  constructor.
  + by apply himpl; [left; reflexivity..|].
  apply ih.
  move=> a' b' c' ????.
  by apply himpl; [right..|].
Qed.

Lemma get_pi_Forall :
  List.Forall (fun '(x, (opi, (v1, v2))) =>
    forall pi, opi = Some pi -> get_pi x.(v_var) = Some (pi, (v1, v2)))
    (zip params (zip sao.(sao_params) (zip vargs1 vargs2))).
Proof.
  apply List.Forall_forall.
  move=> [x [opi [v1 v2]]] hin pi ?; subst opi.
  rewrite /get_pi.
  apply: mem_uniq_assoc uniq_param_tuples.
  rewrite /param_tuples.
  have [s1 [s2 ->]] := List.in_split _ _ hin.
  rewrite pmap_cat.
  by apply List.in_app_iff; right; left.
Qed.

(*
Section bla.


(* can we get rid of inversion? *)
Lemma get_pi_test :
  Forall3 (fun (x:var_i) opi v2 =>
    exists v1, [/\
      Rin_aux (emem s2) opi v1 v2,
      (opi <> None -> subtype x.(vtype) (type_of_val v1)) &
      exists i, [/\
        oseq.onth params i = Some x,
        nth None sao.(sao_params) i = opi,
        nth (Vbool true) vargs1 i = v1 &
        nth (Vbool true) vargs2 i = v2]])
  params sao.(sao_params) vargs2.
Proof.
  move: hparams.
  elim: Hrin params Hsub vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params.
  + by move=> [|//]; constructor.
  move=> opi varg1 varg2 sao_params vargs1' vargs2' h1 h2 ih [//|x params'] hsub.
  rewrite /init_params /=.
  t_xrbindP=> _ _ _ _ _ _ _ [[[_ _] _] _] _ _ _ [[[_ _] _] _] /ih{ih}ih _ _.
  constructor => //.
  + exists varg1; split=> //.
    + by inversion hsub.
    by exists 0%nat.
  apply: Forall3_impl (ih _).
  + move=> x' opi' v2' [v1 [?? [i ?]]].
    exists v1; split=> //.
    by exists (S i).
  by inversion hsub.
Qed.

Lemma zip_map_l A B C (f : A -> C) (l1:seq A) (l2:seq B) :
  zip (map f l1) l2 = map (fun x => (f x.1, x.2)) (zip l1 l2).
Proof.
  elim: l1 l2 => [|a1 l1 ih] [|a2 l2] //=.
  f_equal.
  by apply ih.
Qed.
*)
(*
Hypothesis Hdisjoint : forall s1 pi1 v1 w1 s2 pi2 v2 w2,
  get_pi s1 = Some (pi1, (v1, @Vword Uptr w1)) ->
  get_pi s2 = Some (pi2, (v2, @Vword Uptr w2)) ->
  s1 <> s2 ->
  disjoint_zrange w1 (size_slot s1) w2 (size_slot s2).
*)

(* We perform an induction while we could use properties of zip and List.In,
   but it seems simpler in this case.
*)
Lemma get_pi_wf_arg s pi v1 v2 :
  get_pi s = Some (pi, (v1, v2)) -> wf_arg glob_size rip m1 m2 (Some pi) v1 v2.
Proof.
  rewrite /get_pi => -/(assoc_mem' (w:=_)).
  rewrite /param_tuples.
  elim: Hargs params; first by move=> [].
  move=> opi varg1 varg2 sao_params vargs1' vargs2' hrin _ ih [//|param params'].
  case: opi hrin => [pi'|] hrin; last by apply ih.
  by move=> [[_ <- <- <-] //|]; apply ih.
Qed.

Lemma get_pi_size_le s pi v1 v2 :
  get_pi s = Some (pi, (v1, v2)) -> size_slot s <= size_val v1.
Proof.
  rewrite /get_pi => -/(assoc_mem' (w:=_)).
  rewrite /param_tuples.
  elim: Hsub vargs2; first by move=> [].
  move=> opi x varg1 sao_params params' vargs1' hsub _ ih [//|varg2 vargs2'].
  case: opi hsub => [pi'|] hsub; last by apply ih.
  move=> [[<- _ <- _] //|]; last by apply ih.
  apply size_of_le.
  by apply hsub.
Qed.

Lemma get_pi_nth s pi v1 v2 :
  get_pi s = Some (pi, (v1, v2)) ->
  exists k,
    [/\ nth vrip0 (map v_var params) k = s,
        nth None sao.(sao_params) k = Some pi,
        nth (Vbool true) vargs1 k = v1 &
        nth (Vbool true) vargs2 k = v2].
Proof.
  rewrite /get_pi => -/(assoc_mem' (w:=_)).
  rewrite /param_tuples.
  elim: sao.(sao_params) params vargs1 vargs2; first by move=> [|??] [|??] [|??].
  move=> opi sao_params ih [|x params'] [|varg1 vargs1'] [|varg2 vargs2'] //.
  case: opi => [pi'|].
  + move=> /=.
    case.
    + by move=> [-> -> -> ->]; exists 0%nat.
    by move=> /ih{ih} [k ih]; exists (S k).
  by move=> /ih{ih} [k ih]; exists (S k).
Qed.

(*
Lemma init_params_get_pi pi :
  List.In (Some pi) (sao.(sao_params)) -> get_pi pi.(pp_ptr) = Some pi.
Proof.
  have: List.In (Some pi) sao.(sao_params) ->
    get_pi pi.(pp_ptr) = Some pi /\ ~ Sv.In pi.(pp_ptr) vnew1;
  last first.
  + by move=> h /h [].
  rewrite /get_pi.
  move: hparams; rewrite /init_params.
  elim: sao.(sao_params) params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params => //.
  move=> opi2 sao_params ih [//|param params'].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' /=.
  t_xrbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param'].
  case: opi2 => [pi2|]; last first.
  + by move=> [<- _ _ _] [[[??]?]?] /ih{ih}ih _ _ [//|] /ih.
  t_xrbindP=> _ _ _ /assertP /Sv_memP hnnew _ _ _ _.
  case: Mvar.get=> //.
  case: Mvar.get=> //.
  case: Mvar.get=> //.
  move=> [? _ _ _]; subst vnew1'.
  move=> {vnew2' locals2' rmap2' alloc_params'}
    [[[vnew2' locals2'] rmap2'] alloc_params2'] /ih{ih}ih _ _.
  case.
  + by move=> [?]; subst pi2; rewrite eq_refl; split.
  move=> /ih{ih}[ih1 ih2].
  case: eqP => [heq|_].
  + by case ih2; apply Sv.add_spec; left.
  split=> //.
  move=> hnew.
  by case ih2; apply Sv.add_spec; right.
Qed.

Lemma get_piP s pi :
  get_pi s = Some pi <-> List.In (Some pi) sao.(sao_params) /\ s = pi.(pp_ptr).
Proof.
  split; last first.
  + by move=> [hin ->]; apply init_params_get_pi.
  rewrite /get_pi.
  case hfind: List.find => [[pi2|//]|//] [?]; subst pi2.
  by have [? /eqP ?] := List.find_some _ _ hfind.
Qed.
*)
Lemma disjoint_globals_params : disjoint Slots_globals Slots_params.
Proof.
  apply /disjointP => s /in_Slots_slots ? /in_Slots_params.
  case heq: get_pi => [pi|//].
  by have [] := init_params_not_glob_nor_stack heq; congruence.
Qed.

Lemma disjoint_locals_params : disjoint Slots_locals Slots_params.
Proof.
  apply /disjointP => s /in_Slots_slots ? /in_Slots_params.
  case heq: get_pi => [pi|//].
  by have [] := init_params_not_glob_nor_stack heq; congruence.
Qed.

Lemma pick_slot_params s :
  Sv.In s Slots_params ->
  forall A (f_globals f_locals f_params : slot -> A),
  pick_slot f_globals f_locals f_params s = f_params s.
Proof.
  rewrite /pick_slot.
  case: Sv_memP => [|_].
  + by move /disjointP : disjoint_globals_params => h /h.
  case: Sv_memP => //.
  by move /disjointP : disjoint_locals_params => h /h.
Qed.

Lemma disjoint_zrange_globals_params :
  forall s, Sv.In s Slots_params -> Writable_params s ->
  0 < glob_size -> disjoint_zrange rip glob_size (Addr_params s) (size_slot s).
Proof.
  move=> s hin hw hgsize.
  have /in_Slots_params := hin.
  case hpi: get_pi => [[pi [varg1 varg2]]|//] _.
  rewrite /Addr_params hpi.
  have /= := get_pi_wf_arg hpi.
  move=> [p [? hargp]]; subst varg2.
  move: hw; rewrite /Writable_params hpi => hw.
  have := hargp.(wap_writable_not_glob) hw hgsize.
  apply disjoint_zrange_incl_r.
  by apply: zbetween_le (get_pi_size_le hpi).
Qed.

Hypothesis Hdisjoint_zrange_locals :
  Forall3 (fun opi varg1 varg2 =>
    forall pi, opi = Some pi ->
    forall (p:ptr), varg2 = Vword p ->
    0 < sao.(sao_size) ->
    disjoint_zrange rsp sao.(sao_size) p (size_val varg1)) sao.(sao_params) vargs1 vargs2.

Lemma disjoint_zrange_locals_params :
  forall s, Sv.In s Slots_params -> 0 < sao.(sao_size) ->
  disjoint_zrange rsp sao.(sao_size) (Addr_params s) (size_slot s).
Proof.
  move=> s hin hlt.
  have /in_Slots_params := hin.
  case hpi: get_pi => [[pi [varg1 varg2]]|//] _.
  rewrite /Addr_params hpi.
  have /= := get_pi_wf_arg hpi.
  move=> [p [? hargp]]; subst varg2.
  have hle := get_pi_size_le hpi.
  apply (disjoint_zrange_incl_r (zbetween_le _ hle)).
  have [k [hnth1 hnth2 hnth3 hnth4]] := get_pi_nth hpi.
  rewrite -hnth3.
  by apply (Forall3_nth Hdisjoint_zrange_locals None (Vbool true) (Vbool true)
    (nth_not_default hnth2 ltac:(discriminate)) _ hnth2 _ hnth4 hlt).
Qed.

(* TODO: clean? *)
Lemma wf_Slots_params :
  wf_Slots Slots_params Addr_params Writable_params Align_params.
Proof.
  split.
  + move=> s /in_Slots_params.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [p [? hargp]] := get_pi_wf_arg hpi; subst v2.
    have hle := get_pi_size_le hpi.
    rewrite /Addr_params hpi.
    apply: no_overflow_incl hargp.(wap_no_overflow).
    by apply zbetween_le.
  + move=> sl1 sl2 /in_Slots_params hsl1 /in_Slots_params hsl2 hneq.
    case hpi1: get_pi hsl1 => [[pi1 [v11 v12]]|//] _.
    case hpi2: get_pi hsl2 => [[pi2 [v21 v22]]|//] _.
    have [p1 [? hargp1]] := get_pi_wf_arg hpi1; subst v12.
    have [p2 [? hargp2]] := get_pi_wf_arg hpi2; subst v22.
    rewrite /Writable_params /Addr_params !hpi1 hpi2 => hw1.
    have hle1 := get_pi_size_le hpi1.
    have hle2 := get_pi_size_le hpi2.
    have [k1 [hnth11 hnth12 hnth13 hnth14]] := get_pi_nth hpi1.
    have [k2 [hnth21 hnth22 hnth23 hnth24]] := get_pi_nth hpi2.
    have := Hdisj hnth12 hnth14 hnth22 hnth24 ltac:(congruence) hw1.
    rewrite hnth13 hnth23.
    by apply: disjoint_zrange_incl; apply zbetween_le.
  + move=> s /in_Slots_params.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [p [? hargp]] := get_pi_wf_arg hpi; subst v2.
    rewrite /Addr_params /Align_params hpi.
    by apply hargp.(wap_align).
  by apply disjoint_zrange_globals_params.
Qed.

(* il faut faire des hyps sur params :
   - Rin_aux ?
   - les sr sont disjoints des locaux (sera garanti par alloc_stack qui alloue mem fresh
   - disjoint entre eux
*)
Lemma Haddr_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s).
Proof.
  move=> s /in_Slots [hin|[hin|hin]].
  + rewrite /Addr (pick_slot_globals hin).
    apply: no_overflow_incl no_overflow_glob_size.
    by apply zbetween_Addr_globals.
  + rewrite /Addr (pick_slot_locals hin).
    apply: no_overflow_incl no_overflow_size.
    by apply zbetween_Addr_locals.
  rewrite /Addr (pick_slot_params hin).
  by apply wf_Slots_params.
Qed.

(* TODO: clean *)
Lemma Hdisjoint_writable : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
  Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2).
Proof.
  move=> sl1 sl2 hin1 hin2 hneq hw.
  have hover1 := Haddr_no_overflow hin1.
  have hover2 := Haddr_no_overflow hin2.
  move /in_Slots : hin1 => [hin1|[hin1|hin1]].
  + by move: hw; rewrite /Writable (pick_slot_globals hin1).
  + move /in_Slots : hin2 => [hin2|[hin2|hin2]].
    + apply disjoint_zrange_sym.
      apply: disjoint_zrange_incl (disjoint_zrange_globals_locals _ _).
      + rewrite /Addr (pick_slot_globals hin2).
        by apply (zbetween_Addr_globals hin2).
      + rewrite /Addr (pick_slot_locals hin1).
        by apply (zbetween_Addr_locals hin1).
      + move /in_Slots_slots : hin2.
        case heq: Mvar.get => [[ofs ws]|//] _.
        have := init_map_bounded heq.
        have := size_slot_gt0 sl2.
        by lia.
      move /in_Slots_slots : hin1.
      case heq: Mvar.get => [[ofs ws]|//] _.
      have := init_stack_layout_bounded heq.
      have := size_slot_gt0 sl1.
      by lia.
    + split=> //.
      rewrite /Addr (pick_slot_locals hin1) (pick_slot_locals hin2).
      move /in_Slots_slots : hin1.
      case heq1 : Mvar.get => [[ofs1 ws1]|//] _.
      move /in_Slots_slots : hin2.
      case heq2 : Mvar.get => [[ofs2 ws2]|//] _.
      rewrite (wunsigned_Addr_locals heq1).
      rewrite (wunsigned_Addr_locals heq2).
      have := init_stack_layout_disjoint heq1 heq2 hneq.
      by lia.
    rewrite /Addr (pick_slot_locals hin1) (pick_slot_params hin2).
    apply: disjoint_zrange_incl_l (disjoint_zrange_locals_params hin2 _).
    + by apply (zbetween_Addr_locals hin1).
    move /in_Slots_slots : hin1.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_stack_layout_bounded heq.
    have := size_slot_gt0 sl1.
    by lia.
  move /in_Slots : hin2 => [hin2|[hin2|hin2]].
  + rewrite /Addr (pick_slot_params hin1) (pick_slot_globals hin2).
    rewrite /Writable (pick_slot_params hin1) in hw.
    apply disjoint_zrange_sym.
    apply: disjoint_zrange_incl_l (disjoint_zrange_globals_params hin1 hw _).
    + by apply (zbetween_Addr_globals hin2).
    move /in_Slots_slots : hin2.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_map_bounded heq.
    have := size_slot_gt0 sl2.
    by lia.
  + rewrite /Addr (pick_slot_params hin1) (pick_slot_locals hin2).
    apply disjoint_zrange_sym.
    apply: disjoint_zrange_incl_l (disjoint_zrange_locals_params hin1 _).
    + by apply (zbetween_Addr_locals hin2).
    move /in_Slots_slots : hin2.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_stack_layout_bounded heq.
    have := size_slot_gt0 sl2.
    by lia.
  rewrite /Addr (pick_slot_params hin1) (pick_slot_params hin2).
  rewrite /Writable (pick_slot_params hin1) in hw.
  by apply wf_Slots_params.
Qed.

Lemma Hslot_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s).
Proof.
  move=> s /in_Slots [hin|[hin|hin]].
  + rewrite /Addr /Align !(pick_slot_globals hin).
    move /in_Slots_slots : hin.
    case heq: Mvar.get => [[ofs ws]|//] _.
    rewrite /Addr_globals /Offset_slots /Align_globals /Align_slots heq.
    apply is_align_add.
    + apply: is_align_m rip_align.
      by apply wsize_ge_U256.
    rewrite WArray.arr_is_align.
    by apply /eqP; apply (init_map_align heq).
  + rewrite /Addr /Align !(pick_slot_locals hin).
    move /in_Slots_slots : hin.
    case heq: Mvar.get => [[ofs ws]|//] _.
    rewrite /Addr_locals /Offset_slots /Align_locals /Align_slots heq.
    apply is_align_add.
    + apply: is_align_m rsp_align.
      by apply (init_stack_layout_stack_align heq).
    rewrite WArray.arr_is_align.
    by apply /eqP; apply (init_stack_layout_align heq).
  rewrite /Addr /Align !(pick_slot_params hin).
  by apply wf_Slots_params.
Qed.

Lemma Hwritable_not_glob :
  forall s, Sv.In s Slots -> Writable s ->
  0 < glob_size -> disjoint_zrange rip glob_size (Addr s) (size_slot s).
Proof.
  move=> s /in_Slots [hin|[hin|hin]].
  + by rewrite /Writable (pick_slot_globals hin).
  + move=> _ hlt.
    apply: disjoint_zrange_incl_r (disjoint_zrange_globals_locals _ _).
    + rewrite /Addr (pick_slot_locals hin).
      by apply (zbetween_Addr_locals hin).
    + done.
    move /in_Slots_slots : hin.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_stack_layout_bounded heq.
    have := size_slot_gt0 s.
    by lia.
  rewrite /Writable /Addr !(pick_slot_params hin).
  by apply wf_Slots_params.
Qed.

Lemma Hwf_Slots : wf_Slots Slots Addr Writable Align.
Proof.
  split.
  + by apply Haddr_no_overflow.
  + by apply Hdisjoint_writable.
  + by apply Hslot_align.
  by apply Hwritable_not_glob.
Qed.

(* End bla. *)

Definition lmap locals' vnew' := {|
  vrip := vrip0;
  vrsp := vrsp0;
  globals := mglob;
  locals := locals';
  vnew := vnew'
|}.

Lemma init_map_wf g ofs ws :
  Mvar.get mglob g = Some (ofs, ws) ->
  wf_global rip Slots Addr Writable Align g ofs ws.
Proof.
  move=> hget.
  have hin: Sv.In g Slots_globals.
  + by apply in_Slots_slots; congruence.
  split=> /=.
  + by apply in_Slots; left.
  + by rewrite /Writable (pick_slot_globals hin).
  + by rewrite /Align (pick_slot_globals hin) /Align_globals /Align_slots hget.
  by rewrite /Addr (pick_slot_globals hin) /Addr_globals /Offset_slots hget.
Qed.

Lemma init_map_wf_rmap vnew' s1 s2 :
  (forall i, 0 <= i < glob_size ->
    read (emem s2) (rip + wrepr U64 i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) ->
  wf_rmap (lmap (Mvar.empty _) vnew') Slots Addr Writable Align P empty s1 s2.
Proof.
  move=> heqvalg.
  split=> //=.
  move=> y sry bytesy vy.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => // hg.
  case heq: Mvar.get => [[ofs ws]|//] [<- <-].
  rewrite get_gvar_glob // => /get_globalI [v [hv -> hty]].
  split=> // off _ w hget.
  rewrite /sub_region_addr /= wrepr0 GRing.addr0.
  have hin: Sv.In y.(gv) Slots_globals.
  + by apply in_Slots_slots; congruence.
  rewrite /Addr (pick_slot_globals hin) /Addr_globals /Offset_slots heq.
  rewrite -GRing.addrA -wrepr_add.
  rewrite heqvalg.
  + f_equal.
    have /check_globsP := hv.
    rewrite heq => -[? [? [[<- _]]]].
    by apply.
  have := init_map_bounded heq.
  have := get_val_byte_bound hget; rewrite hty.
  by lia.
Qed.

Lemma add_alloc_wf_pmap locals1' rmap1' vnew1' x pki locals2' rmap2' vnew2' :
  add_alloc fn mglob stack (x, pki) (locals1', rmap1', vnew1') = ok (locals2', rmap2', vnew2') ->
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  wf_pmap (lmap locals2' vnew2') rsp rip Slots Addr Writable Align.
Proof.
  move=> hadd hpmap.
  case: (hpmap) => /= hrip hrsp hnew1 hnew2 hglobals hlocals hnew.
  move: hadd => /=.
  case: Sv_memP => [//|hnnew].
  case hregx: Mvar.get => //.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> {rmap2'} -[[sv pk] rmap2'] hpki [<- _ <-].
  case: pki hpki.
  + move=> s z sc.
    case heq: Mvar.get => [[ofs ws]|//].
    case: ifP => [/and3P []|//].
    rewrite !Zcmp_le !zify => h1 h2 h3 [<- <- _].
    split=> //=.
    + move=> y pky.
      rewrite Mvar.setP.
      case: eqP.
      + move=> <- [<-].
        case: sc heq => heq.
        + have hin: Sv.In s Slots_locals.
          + by apply in_Slots_slots; congruence.
          split=> //=.
          + by apply in_Slots; right; left.
          + by rewrite /Writable (pick_slot_locals hin).
          + by rewrite /Align (pick_slot_locals hin) /Align_locals /Align_slots heq.
          by rewrite /Addr (pick_slot_locals hin) /Addr_locals /Offset_slots heq.
        have hin: Sv.In s Slots_globals.
        + by apply in_Slots_slots; congruence.
        split=> //=.
        + by apply in_Slots; left.
        + by rewrite /Writable (pick_slot_globals hin).
        + by rewrite /Align (pick_slot_globals hin) /Align_globals /Align_slots heq.
        by rewrite /Addr (pick_slot_globals hin) /Addr_globals /Offset_slots heq.
      move=> hneq /hlocals.
      case: pky => //=.
      + move=> p [] hty1 hty2 hrip' hrsp' hnew' hneq'.
        split=> //=.
        rewrite /get_local /= => w wr.
        rewrite Mvar.setP.
        case: eqP => //.
        by move=> _; apply hneq'.
      move=> sy ofsy wsy zy yf [] hslot hty hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
      split=> //=.
      rewrite /get_local /= => w sw ofsw wsw zw wf.
      rewrite Mvar.setP.
      case: eqP => //.
      by move=> _; apply hneq'.
    move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + by move=> <- _.
    by move=> _; apply hnew.
  + move=> p.
    case harr: is_sarr => //=.
    case: Sv_memP => [//|hnnew2].
    case heq0: Mvar.get => //.
    case: eqP => [hty|//] /= [<- <- _].
    split=> //=.
    + by apply SvD.F.add_2.
    + by apply SvD.F.add_2.
    + move=> y pky.
      rewrite Mvar.setP.
      case: eqP.
      + move=> <- [<-].
        split=> //=.
        + by congruence.
        + by congruence.
        + by apply SvD.F.add_1.
        rewrite /get_local /= => w wr.
        rewrite Mvar.setP.
        case: eqP => //.
        by move=> hneq /hlocals /wfr_new /=; congruence.
      move=> hneq /hlocals.
      case: pky => //=.
      + move=> p' [] /= hty1 hty2 hrip' hrsp' hnew' hneq'.
        split=> //=.
        + by apply SvD.F.add_2.
        rewrite /get_local /= => w wr.
        rewrite Mvar.setP.
        case: eqP.
        + by move=> _ [<-]; congruence.
        by move=> _; apply hneq'.
      move=> sy ofsy wsy zy yf [] hslot hty' hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
      split=> //=.
      + by apply SvD.F.add_2.
      move=> w sw ofsw wsw zw wf.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _; apply hneq'.
    move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- _.
      have ?: x <> p.
      + by move /is_sarrP: harr => [n]; congruence.
      by move=> /SvD.F.add_3; auto.
    move=> ? /dup[] ? /hnew ?.
    have ?: p <> y by congruence.
    by move=> /SvD.F.add_3; auto.
  move=> s z f.
  case harr: is_sarr => //.
  case heq: Mvar.get => [[ofs ws]|//].
  case: Sv_memP => [//|hnnew2].
  case: eqP => [//|hneq0].
  case heqf: Mvar.get => //.
  case: ifP => [/and5P []|//].
  move=> h1.
  rewrite !Zcmp_le !zify.
  move=> h2 /eqP; rewrite (Zland_mod _ U64) => h3 h4 h5 [<- <- _].
  split=> //=.
  + by apply SvD.F.add_2.
  + by apply SvD.F.add_2.
  + move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- [<-].
      have hin: Sv.In s Slots_locals.
      + by apply in_Slots_slots; congruence.
      split=> //=.
      + by apply in_Slots; right; left.
      + by rewrite /Writable (pick_slot_locals hin).
      + by rewrite /Align (pick_slot_locals hin) /Align_locals /Align_slots heq.
      + by rewrite WArray.arr_is_align; apply /eqP.
      + by rewrite /Addr (pick_slot_locals hin) /Addr_locals /Offset_slots heq.
      + by apply SvD.F.add_1.
      move=> w sw ofsw wsw zw wf.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _ /hlocals /wfs_new /=; congruence.
    move=> hneq /hlocals.
    case: pky => //=.
    + move=> p [] hty1 hty2 hrip' hrsp' hnew' hneq'.
      split=> //=.
      + by apply SvD.F.add_2.
      move=> w wr /=.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _; apply hneq'.
    move=> sy ofsy wsy zy yf [] /= hslot hty' hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
    split=> //=.
    + by apply SvD.F.add_2.
    move=> w sw ofsw wsw zw wf.
    rewrite /get_local /= Mvar.setP.
    case: eqP.
    + by move=> _ [_ _ _ _ <-]; congruence.
    by move=> _; apply hneq'.
  move=> y pky.
  rewrite Mvar.setP.
  case: eqP.
  + move=> <- _.
    by move=> /SvD.F.add_3; auto.
  move=> ? /dup[] ? /hnew ?.
  have ?: f <> y by congruence.
  by move=> /SvD.F.add_3; auto.
Qed.

Lemma add_alloc_wf_rmap locals1' rmap1' vnew1' x pki locals2' rmap2' vnew2' s2 :
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  add_alloc fn mglob stack (x, pki) (locals1', rmap1', vnew1') = ok (locals2', rmap2', vnew2') ->
  let: s1 := {| emem := m1; evm := vmap0 |} in
  wf_rmap (lmap locals1' vnew1') Slots Addr Writable Align P rmap1' s1 s2 ->
  wf_rmap (lmap locals2' vnew2') Slots Addr Writable Align P rmap2' s1 s2.
Proof.
  move=> hpmap hadd hrmap.
  case: (hrmap) => hwfsr hval hptr.
  move: hadd => /=.
  case: Sv_memP => [//|hnnew].
  case hregx: Mvar.get => //.
  set wf_rmap := wf_rmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> {rmap2'} -[[sv pk] rmap2'] hpki [<- <- <-].
  case: pki hpki.
  + move=> s z sc.
    case heq: Mvar.get => [[ofs ws]|//].
    case: ifP => [/and3P []|//].
    rewrite !Zcmp_le !zify => h1 h2 h3 [<- <- <-].
    case: sc heq => heq.
    + split.
      + move=> y sry.
        rewrite Mvar.setP.
        case: eqP.
        + move=> <- [<-].
          have hin: Sv.In s Slots_locals.
          + by apply in_Slots_slots; congruence.
          split; split=> //=.
          + by apply in_Slots; right; left.
          + by rewrite /Writable (pick_slot_locals hin).
          by rewrite /Align (pick_slot_locals hin) /Align_locals /Align_slots heq.
        by move=> _; apply hwfsr.
      + move=> y sry bytesy vy /check_gvalid_set_move [].
        + move=> [hg ? _ _]; subst x.
          rewrite get_gvar_nglob; last by apply /negP.
          rewrite /get_var /= Fv.get0.
          case: vtype => //= len [<-].
          split=> // off _ w /=.
          rewrite WArray.get_empty.
          by case: ifP.
        by move=> [] _; apply hval.
      move=> y sry.
      rewrite /get_local /=.
      rewrite !Mvar.setP.
      case: eqP.
      + move=> _ [<-].
        by eexists.
      move=> hneq /hptr [pky [hly hpky]].
      exists pky; split=> //.
      case: pky hly hpky => //= sy ofsy wsy zy yf hly hpky.
      rewrite /check_stack_ptr get_var_bytes_set_move_bytes /=.
      case: eqP => //=.
      case: eqP => //.
      by have /wf_locals /wfs_new /= := hly; congruence.
    split=> //.
    move=> y sry /hptr.
    rewrite /get_local /= => -[pky [hly hpky]].
    exists pky; split=> //.
    rewrite Mvar.setP.
    by case: eqP; first by congruence.
  + move=> p.
    case harr: is_sarr => //=.
    case: Sv_memP => [//|hnnew2].
    case heq0: Mvar.get => //.
    case: eqP => [hty|//] /= [<- <- <-].
    split=> //=.
    move=> y sry /hptr.
    rewrite /get_local /= => -[pky [hly hpky]].
    exists pky; split=> //.
    rewrite Mvar.setP.
    by case: eqP; first by congruence.
  move=> s z f.
  case harr: is_sarr => //.
  case heq: Mvar.get => [[ofs ws]|//].
  case: Sv_memP => [//|hnnew2].
  case: eqP => [//|hneq0].
  case heqf: Mvar.get => //.
  case: ifP => [/and5P []|//].
  move=> h1.
  rewrite !Zcmp_le !zify.
  move=> h2 /eqP; rewrite (Zland_mod _ U64) => h3 h4 h5 [<- <- <-].
  split=> //.
  move=> y sry /hptr.
  rewrite /get_local /= => -[pky [hly hpky]].
  exists pky; split=> //.
  rewrite Mvar.setP.
  by case: eqP; first by congruence.
Qed.

Lemma init_local_map_wf_pmap :
  wf_pmap (lmap locals1 vnew1) rsp rip Slots Addr Writable Align.
Proof.
  move: hlocal_map; rewrite /init_local_map.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] hfold [???]; subst locals1' rmap1' vnew1'.
  move: hfold.
  have: wf_pmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).2) rsp rip
                      Slots Addr Writable Align.
  + split=> //=.
    + by apply SvD.F.add_1.
    + by apply SvD.F.add_2; apply SvD.F.add_1.
    by apply init_map_wf.
  elim: sao.(sao_alloc) (Mvar.empty _, _, _).
  + by move=> /= [[locals0 rmap0] vnew0] ? [<- _ <-].
  move=> [x pki] l ih [[locals0 rmap0] vnew0] /= hpmap.
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] halloc.
  apply ih.
  by apply (add_alloc_wf_pmap halloc hpmap).
Qed.

Lemma init_local_map_wf_rmap s2 :
  let: s1 := {| emem := m1; evm := vmap0 |} in
  (forall i, 0 <= i < glob_size ->
    read (emem s2) (rip + wrepr U64 i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) ->
  wf_rmap (lmap locals1 vnew1) Slots Addr Writable Align P rmap1 s1 s2.
Proof.
  move=> heqvalg.
  move: hlocal_map; rewrite /init_local_map.
  set wf_rmap := wf_rmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] hfold [???]; subst locals1' rmap1' vnew1'.
  move: hfold.
  have: wf_pmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).2) rsp rip
                      Slots Addr Writable Align
     /\ wf_rmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).2)
                Slots Addr Writable Align P (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).1.2 {| emem := m1; evm := vmap0 |} s2.
  + split.
    + split=> //=.
      + by apply SvD.F.add_1.
      + by apply SvD.F.add_2; apply SvD.F.add_1.
      by apply init_map_wf.
    by apply init_map_wf_rmap.
  elim: sao.(sao_alloc) (Mvar.empty _, _, _).
  + by move=> /= [[locals0 rmap0] vnew0] [??] [<- <- <-].
  move=> [x pki] l ih [[locals0 rmap0] vnew0] /= [hpmap hrmap].
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] halloc.
  apply ih.
  split.
  + apply (add_alloc_wf_pmap halloc hpmap).
  by apply (add_alloc_wf_rmap hpmap halloc hrmap).
Qed.

Lemma init_param_wf_pmap vnew1' locals1' rmap1' sao_param (param:var_i) vnew2' locals2' rmap2' alloc_param :
  init_param mglob stack (vnew1', locals1', rmap1') sao_param param =
    ok (vnew2', locals2', rmap2', alloc_param) ->
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  wf_pmap (lmap locals2' vnew2') rsp rip Slots Addr Writable Align.
Proof.
  move=> hparam hpmap.
  case: (hpmap) => /= hrip hrsp hnew1 hnew2 hglobals hlocals hnew.
  move: hparam => /=.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> _ /assertP /Sv_memP hnnew.
  case heq: Mvar.get => //.
  case: sao_param => [pi|[<- <- _ _] //].
  t_xrbindP=> _ /assertP /eqP hregty _ /assertP /Sv_memP hnnew2 _ /assertP harrty.
  case heq1: Mvar.get => //.
  case heq2: Mvar.get => //.
  case heq3: Mvar.get => //.
  move=> [<- <- _ _].
  split=> //=.
  + by apply SvD.F.add_2.
  + by apply SvD.F.add_2.
  + move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- [<-] /=.
      split=> //=.
      + by congruence.
      + by congruence.
      + by apply SvD.F.add_1.
      move=> w wr.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _ /hlocals /wfr_new /=; congruence.
    move=> ? /hlocals.
    case: pky => //=.
    + move=> p [] /= hty1 hty2 hrip' hrsp' hnew' hneq'.
      split=> //=.
      + by apply SvD.F.add_2.
      move=> w wr.
      rewrite /get_local /= Mvar.setP.
      case: eqP.
      + by move=> _ [<-]; congruence.
      by move=> _; apply hneq'.
    move=> sy ofsy wsy zy yf [] /= hslot hty' hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
    split=> //=.
    + by apply SvD.F.add_2.
    move=> w sw ofsw wsw zw wf.
    rewrite /get_local /= Mvar.setP.
    case: eqP => //.
    by move=> _; apply hneq'.
  move=> y pky.
  rewrite Mvar.setP.
  case: eqP.
  + move=> <- _.
    have ?: param.(v_var) <> pi.(pp_ptr).
    + by move /is_sarrP : harrty => [n]; congruence.
    by move=> /SvD.F.add_3; auto.
  move=> ? /dup[] ? /hnew ?.
  have ?: pi.(pp_ptr) <> y by congruence.
  by move=> /SvD.F.add_3; auto.
Qed.

Lemma valid_state_init_param rmap m0 s1 s2 vnew1' locals1' sao_param (param:var_i) vnew2' locals2' rmap2' alloc_param :
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  valid_state (lmap locals1' vnew1') glob_size rsp rip Slots Addr Writable Align P rmap m0 s1 s2 ->
  init_param mglob stack (vnew1', locals1', rmap) sao_param param = ok (vnew2', locals2', rmap2', alloc_param) ->
  forall s1' varg1 varg2,
  write_var param varg1 s1 = ok s1' ->
  (forall pi, sao_param = Some pi -> get_pi param = Some (pi, (varg1, varg2))) ->
  wf_arg glob_size rip (emem s1) (emem s2) sao_param varg1 varg2 ->
  exists s2',
  write_var alloc_param.2 varg2 s2 = ok s2' /\
  valid_state (lmap locals2' vnew2') glob_size rsp rip Slots Addr Writable Align P rmap2' m0 s1' s2'.
Proof.
  move=> hpmap hvs hparam.
  have hpmap2 := init_param_wf_pmap hparam hpmap.
  move: hparam => /=.
  t_xrbindP=> _ /assertP /Sv_memP hnnew.
  case heq1: Mvar.get => [//|].
  case: sao_param => [pi|]; last first.
  + move=> [<- <- <- <-].
    move=> s1' varg1 varg2 hw _ ->.
    move: hw.
    rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
    by apply: set_varP hvm1 => [v' hv <- | hb hv <-]; rewrite /write_var /set_var hv /= ?hb /=;
      eexists;(split;first by reflexivity); apply valid_state_set_var.
  t_xrbindP=> _ /assertP /eqP hty1 _ /assertP /Sv_memP hnnew2 _ /assertP /is_sarrP [n hty2].
  case heq2: Mvar.get => //.
  case heq3: Mvar.get => //.
  case heq4: Mvar.get => //.
  move=> [? ? <- <-]; subst vnew2' locals2'.
  move=> s1' varg1 varg2 hw /(_ _ refl_equal) hpi [w [? hargp]]; subst varg2.
  rewrite /write_var /set_var /=.
  case: pi.(pp_ptr) hty1 hpmap2 => /= _ pin -> /=.
  set p := {| vname := pin |} => hpmap2.
  eexists; split; first by reflexivity.
  move: hw; rewrite /write_var.
  set valid_state := valid_state. (* hack due to typeclass interacting badly *)
  t_xrbindP => vm1 hvm1 <- /=.
  apply: set_varP hvm1; last by rewrite {1}hty2.
  case: param hty2 hnnew heq1 heq3 heq4 hpi hpmap2 => -[_ paramn] paramii /= -> /=.
  set param := {| vname := paramn |} => hnnew heq1 heq3 heq4 hpi hpmap2.
  move=> a1 /to_arrI [n2 [a2 [? hcast]]] <-; subst varg1.
  set sr := sub_region_full _ _.
  have hin: Sv.In sr.(sr_region).(r_slot) Slots_params.
  + by apply in_Slots_params => /=; congruence.
  have hwf: wf_sub_region Slots Writable Align sr (sarr n).
  + split; split=> /=.
    + by apply in_Slots; right; right.
    + by rewrite /Writable (pick_slot_params hin) /Writable_params hpi.
    + by rewrite /Align (pick_slot_params hin) /Align_params hpi.
    + by lia.
    by lia.
  have haddr: w = sub_region_addr Addr sr.
  + rewrite /sub_region_addr /= wrepr0 GRing.addr0.
    by rewrite /Addr (pick_slot_params hin) /= /Addr_params hpi.
  rewrite haddr -(WArray.castK a1).
  apply (valid_state_set_move_regptr hpmap2 (x := param) (v:=Varr a1) (p:=p)) => //; last first.
  + split=> //.
    move=> off _ w' hget.
    rewrite -haddr.
    apply hargp.(wap_read).
    by apply (cast_get8 hcast).
  + by rewrite /get_local /= Mvar.setP_eq.
  case:(hvs) => hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwfr heqmem hglobv htop.
  split=> //.
  + move=> x /=.
    rewrite Mvar.setP.
    case: eqP => //.
    move=> ? hlx hnnew3.
    apply heqvm => //.
    move=> ?; apply hnnew3.
    by apply Sv.add_spec; right.
  case: (hwfr) => hwfsr hval hptr; split=> //.
  + move=> y sry /hptr.
    rewrite /get_local /= => -[pky [hly hpky]].
    exists pky; split=> //.
    rewrite Mvar.setP.
    by case: eqP => //; congruence.
Qed.

Lemma init_params_wf_pmap :
  wf_pmap (lmap locals2 vnew2) rsp rip Slots Addr Writable Align.
Proof.
  move: hparams.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  have := init_local_map_wf_pmap.
  elim: sao.(sao_params) params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params.
  + by move=> [|//] ??????? hbase [<- <- _ _].
  move=> opi sao_params ih [//|param params'].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' hpmap.
  rewrite /init_params /=.
  apply rbindP => -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{ih}ih [<- <- _] _.
  apply ih.
  by apply (init_param_wf_pmap hparam).
Qed.

(* TODO: clean *)
Lemma valid_state_init_params m0 vm1 vm2 :
  let: s1 := {| emem := m1; evm := vm1 |} in
  let: s2 := {| emem := m2; evm := vm2 |} in
  valid_state (lmap locals1 vnew1) glob_size rsp rip Slots Addr Writable Align P rmap1 m0 s1 s2 ->
  forall s1',
  write_vars params vargs1 s1 = ok s1' ->
  exists s2',
  write_vars (map snd alloc_params) vargs2 s2  = ok s2' /\
  valid_state (lmap locals2 vnew2) glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s1' s2'.
Proof.
  move=> hvs.
  have {hvs}:
     wf_pmap (lmap locals1 vnew1) rsp rip Slots Addr Writable Align /\
     valid_state (lmap locals1 vnew1) glob_size rsp rip Slots Addr Writable Align P rmap1 m0 {| emem := m1; evm := vm1 |} {| emem := m2; evm := vm2 |}.
  + split=> //.
    by apply init_local_map_wf_pmap.
  elim: Hargs params get_pi_Forall vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams vm1 vm2.
  + move=> [|//] _ ??????? [<- <- <- <-] vm1 vm2 [_ hvs] _ [<-].
    by eexists.
  move=> opi varg1 varg2 sao_params vargs1' vargs2' hrin _ ih [//|x params'].
  move=> /= /List_Forall_inv [hpi hforall].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{ih}ih [<- <- <-] <- vm1 vm2 [hpmap hvs].
  move=> s1'' s1' hs1' hs1''.
  have [//|s2' [hs2' hvs']] := valid_state_init_param hpmap hvs hparam hs1' _ hrin.
  rewrite /= hs2'.
  move: hs1' hs2'.
  rewrite /write_var.
  t_xrbindP=> /= vm1' hvm1' ? vm2' hvm2' ?; subst s1' s2'.
  have hpmap' := init_param_wf_pmap hparam hpmap.
  have [//|s2'' [hs2'' hvs'']] := ih _ _ _ (conj hpmap' hvs') _ hs1''.
  rewrite hs2''.
  by eexists.
Qed.

Lemma init_param_alloc_param vnew1' locals1' rmap1' sao_param (param:var_i) vnew2' locals2' rmap2' alloc_param :
  init_param mglob stack (vnew1', locals1', rmap1') sao_param param = ok (vnew2', locals2', rmap2', alloc_param) ->
  forall varg1 varg2,
  (forall pi, sao_param = Some pi -> get_pi param = Some (pi, (varg1, varg2))) ->
  forall sr, fst alloc_param = Some sr ->
  varg2 = Vword (sub_region_addr Addr sr).
Proof.
  rewrite /init_param.
  t_xrbindP=> _ _.
  case: Mvar.get => //.
  case: sao_param => [pi|].
  + t_xrbindP => _ _ _ _ _ _.
    case: Mvar.get => //.
    case: Mvar.get => //.
    case: Mvar.get => //.
    move=> [_ _ _ <-] /=.
    move=> varg1 varg2 /(_ _ refl_equal) hpi sr [<-].
    rewrite /sub_region_addr /= wrepr0 GRing.addr0.
    have hin: Sv.In param Slots_params.
    + by apply in_Slots_params; congruence.
    rewrite /Addr (pick_slot_params hin) /Addr_params hpi.
    by have [p [-> _]] := get_pi_wf_arg hpi.
  by move=> [_ _ _ <-].
Qed.

Lemma init_params_alloc_params :
  List.Forall2 (fun osr varg2 => forall sr, osr = Some sr -> varg2 = Vword (sub_region_addr Addr sr)) (map fst alloc_params) vargs2.
Proof.
  elim: Hargs params get_pi_Forall vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams.
  + move=> [|//] _ ??????? [_ _ _ <-].
    by constructor.
  move=> opi varg1 varg2 sao_params vargs1' vargs2' _ _ ih [//|param params'].
  move=> /= /List_Forall_inv [hpi hforall].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{ih}ih _ <- /=.
  constructor; last by apply ih.
  by apply (init_param_alloc_param hparam hpi).
Qed.

Lemma init_params_alloc_params_not_None :
  List.Forall2 (fun osr opi => osr <> None -> opi <> None) (map fst alloc_params) sao.(sao_params).
Proof.
  elim: sao.(sao_params) params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams.
  + move=> [|//] ??????? [_ _ _ <-].
    by constructor.
  move=> opi sao_params ih [//|x params'].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{ih}ih _ <- /=.
  constructor=> //.
  move: hparam.
  t_xrbindP=> _ _.
  case: Mvar.get => //.
  case: opi => [//|].
  by move=> [_ _ _ <-].
Qed.

Lemma init_params_sarr :
  List.Forall2 (fun opi (x:var_i) => opi <> None -> is_sarr x.(vtype)) sao.(sao_params) params.
Proof.
  elim: sao.(sao_params) params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams.
  + by move=> [|//] _ _ _ _ _ _ _ _.
  move=> opi sao_params ih [//|x params'].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[_ _] _] _] /ih{ih}ih _ _.
  constructor=> //.
  move: hparam.
  t_xrbindP=> _ _.
  case: Mvar.get => //.
  case: opi => [pi|//].
  by t_xrbindP=> _ _ _ _ _ /assertP.
Qed.

(*
(* proofs are very similar to add_alloc, can we factorize ? *)
(* TODO: should we prove valid_state instead of wf_rmap ? -> PROBABLY
   should s1 and s2 be the same in hyps and concl ?
*)
Lemma init_param_wf vnew1' locals1' rmap1' sao_param (param:var_i) vnew2' locals2' rmap2' aparam s1 s2 :
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  wf_rmap (lmap locals1' vnew1') Slots Addr Writable Align P rmap1' s1 s2 ->
  (sao_param <> None -> get_pi param = sao_param) ->
  init_param mglob stack (vnew1', locals1', rmap1') sao_param param =
    ok (vnew2', locals2', rmap2', aparam) ->
  wf_pmap (lmap locals2' vnew2') rsp rip Slots Addr Writable Align /\
  wf_rmap (lmap locals2' vnew2') Slots Addr Writable Align P rmap2' s1 s2.
Proof.
  move=> hpmap hrmap.
  case: (hpmap) => /= hrip hrsp hnew1 hnew2 hglobals hlocals hnew.
  case: (hrmap) => hwfsr hval hptr.
  case: sao_param => [pi|? [<- <- <- _] //] /(_ ltac:(discriminate)) hpi.
  t_xrbindP=> _ /assertP /eqP hregty _ /assertP /Sv_memP hnnew _ /assertP harrty
    _ /assertP /Sv_memP hnnew2.
  case heq: Mvar.get => //.
  case heq1: Mvar.get => //.
  case heq2: Mvar.get => //.
  case heq3: Mvar.get => //.
  move=> [<- <- <- _].
  split.
  + split=> //=.
    + by apply SvD.F.add_2.
    + by apply SvD.F.add_2.
    + move=> y pky.
      rewrite Mvar.setP.
      case: eqP.
      + move=> <- [<-] /=.
        split=> //=.
        + by congruence.
        + by congruence.
        + by apply SvD.F.add_1.
        move=> w wr.
        rewrite /get_local /= Mvar.setP.
        case: eqP => //.
        by move=> _ /hlocals /wfr_new /=; congruence.
      move=> ? /hlocals.
      case: pky => //=.
      + move=> p [] /= hty1 hty2 hrip' hrsp' hnew' hneq'.
        split=> //=.
        + by apply SvD.F.add_2.
        move=> w wr.
        rewrite /get_local /= Mvar.setP.
        case: eqP.
        + by move=> _ [<-]; congruence.
        by move=> _; apply hneq'.
      move=> sy ofsy wsy zy yf [] /= hslot hty' hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
      split=> //=.
      + by apply SvD.F.add_2.
      move=> w sw ofsw wsw zw wf.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _; apply hneq'.
    move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- _.
      have ?: param.(v_var) <> pi.(pp_ptr).
      + by move /is_sarrP : harrty => [n]; congruence.
      by move=> /SvD.F.add_3; auto.
    move=> ? /dup[] ? /hnew ?.
    have ?: pi.(pp_ptr) <> y by congruence.
    by move=> /SvD.F.add_3; auto.
  split => /=.
  + move=> y sry.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- [<-].
      have hin: Sv.In param Slots_params.
      + by apply in_Slots_params; congruence.
      split; split=> /=.
      + by apply in_Slots; right; right.
      + rewrite /Writable (pick_slot_params hin) /Writable_params.
        by rewrite hpi.
      + rewrite /Align (pick_slot_params hin) /Align_params.
        by rewrite hpi.
      + by apply Z.le_refl.
      by split; apply Z.le_refl.
    by move=> _; apply hwfsr.
  + move=> y sry bytesy vy /check_gvalid_set_move [].
    + move=> [hg ? _ _]. (* subst param. *)
      admit. (* by move=> /hvm. *)
    by move=> [] _; apply hval.
  move=> y sry.
  rewrite /get_local /=.
  rewrite !Mvar.setP.
  case: eqP.
  + move=> _ [<-].
    eexists; split; first by reflexivity.
    simpl. rewrite /sub_region_addr /= wrepr0 GRing.addr0.
    rewrite /Addr pick_slot_params. (* Rin_aux ?? *) admit.
    apply in_Slots_params. congruence.
  move=> hneq /hptr [pky [hly hpky]].
  exists pky; split=> //.
  case: pky hly hpky => //= sy ofsy wsy zy yf hly hpky.
  rewrite /check_stack_ptr get_var_bytes_set_move_bytes /=.
  case: eqP => //=.
  case: eqP => //.
  by have /hlocals /wfs_new /= := hly; congruence.
Admitted.

Lemma init_params_wf m1 s2 :
  let: s1 := {| emem := m1; evm := vmap0 |} in
(*   (forall x v, get_var s1.(evm) x = ok v -> x = vrip0 \/ x = vrsp0) -> *)
  (forall i, 0 <= i < glob_size ->
    read (emem s2) (rip + wrepr U64 i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) ->
  wf_pmap (lmap locals2 vnew2) rsp rip Slots Addr Writable Align /\
  wf_rmap (lmap locals2 vnew2) Slots Addr Writable Align P rmap2 s1 s2.
Proof.
  move=> heqvalg.
  move: hparams.
  have := init_local_map_wf m1 heqvalg.
  elim: get_pi_params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params.
  + by move=> ??????? hbase [<- <- <- _].
  move=> opi param sao_params params' hpi hforall ih.
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' [hpmap hrmap].
  rewrite /init_params /=.
  t_xrbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] /init_param_wf h.
  move=> [[[??]?]?] /ih{ih}ih [<- <- <-] _.
  apply ih => //.
  by apply h.
Qed.
*)

(* à partir d'ici, on peut raisonner avec rmap2, locals2... *)
(* on peut définir pmap = lmap locals2 vnew2 et montrer wf_pmap pmap grâce à
   init_params_wf
   et définir abréviations valid_state == valid_state Slots Addr ...
   ==> en fait, pas si sûr (ça doit être possible, mais on ne fait pas comme ça)
*)

Record extend_mem (m1 m2:mem) (rip:ptr) (data:seq u8) := {
  em_no_overflow : no_overflow rip (Z.of_nat (size data));
  em_align       : is_align rip U256;
  em_read_old8   : forall p, validw m1 p U8 -> read m1 p U8 = read m2 p U8;
  em_fresh       : forall p, validw m1 p U8 -> disjoint_zrange rip (Z.of_nat (size data)) p (wsize_size U8);
  em_valid       : forall p, validw m1 p U8 || between rip (Z.of_nat (size data)) p U8 -> validw m2 p U8;
  em_read_new    : forall i, 0 <= i < Z.of_nat (size data) ->
                     read m2 (rip + wrepr _ i)%R U8 = ok (nth 0%R data (Z.to_nat i)) }.

(* TODO: remove this hyp and instead assume
  forall s, Sv.In s Slots_params -> validw (Addr s) (size_slot s) ... *)
(*
Hypothesis zbetween_Addr_params :
  forall s, Sv.In s Slots_params ->
  zbetween rip glob_size (Addr_params s) (size_slot s) \/
  zbetween rsp sao.(sao_size) (Addr_params s) (size_slot s).
*)

(* TODO: should we assume init_stk_state = ok ... as section hypothesis and reason about it,
   it would in particular ease the proof of params <> locals, since we would have the properties
   of alloc_stack_spec to reason with. The advantages are not clear. For now, I leave it like this.
*)
(* cf. init_stk_stateI in merge_varmaps_proof *)
(* TODO: clean *)
Lemma init_stk_state_valid_state m3 sz' ws :
  extend_mem m1 m2 rip global_data ->
  alloc_stack_spec m2 ws sao.(sao_size) sz' m3 ->
  rsp = top_stack m3 ->
  vripn <> vrspn ->
  let s2 := {| emem := m3; evm := vmap0.[vrsp0 <- ok (pword_of_word rsp)].[vrip0 <- ok (pword_of_word rip)] |} in
  valid_state (lmap locals1 vnew1) glob_size rsp rip Slots Addr Writable Align P rmap1 m2 {| evm := vmap0; emem := m1 |} s2.
Proof.
  move=> hext hass hrsp hneq /=.
  split.
  + move=> s w /=.
    rewrite hass.(ass_valid).
    case /in_Slots.
    + move=> hin hb.
      apply /orP. left.
      apply hext.(em_valid).
      apply /orP. right.
      apply: zbetween_trans hb.
      rewrite /Addr (pick_slot_globals hin).
      by apply (zbetween_Addr_globals hin).
    case.
    + move=> hin hb.
      apply /orP. right.
      apply: zbetween_trans hb.
      rewrite /Addr (pick_slot_locals hin).
      have := zbetween_Addr_locals hin.
      by rewrite hrsp.
    move=> hin hb /=.
    apply /orP; left.
    have /in_Slots_params := hin.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [p [? hargp]] := get_pi_wf_arg hpi; subst v2.
    have hlt := get_pi_size_le hpi.
    move: hb. rewrite /Addr (pick_slot_params hin) /Addr_params hpi.
    move=> hb. apply hargp.(wap_valid).
    apply: zbetween_trans hb.
    by apply zbetween_le.
  + move=> /= s w hin hvalid.
    case /in_Slots : hin => [hin|[hin|hin]].
    + rewrite /Addr (pick_slot_globals hin).
      apply: (disjoint_zrange_incl_l (zbetween_Addr_globals hin)).
      by apply: hext.(em_fresh) hvalid.
    + rewrite /Addr (pick_slot_locals hin).
      apply: (disjoint_zrange_incl_l (zbetween_Addr_locals hin)).
      have /= := hass.(ass_fresh) (p:=w) (s:=U8).
      rewrite hext.(em_valid); last by rewrite hvalid.
      move=> /(_ erefl) ?.
      split.
      + apply no_overflow_size.
      + apply is_align_no_overflow. apply is_align8.
      rewrite hrsp.
      lia.
    have /in_Slots_params := hin.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [p [? hargp]] := get_pi_wf_arg hpi; subst v2.
    have hle := get_pi_size_le hpi.
    rewrite /Addr (pick_slot_params hin) /Addr_params hpi.
    have := hargp.(wap_fresh) hvalid.
    apply: disjoint_zrange_incl_l.
    by apply zbetween_le.
  + move=> /= p. rewrite hass.(ass_valid) /=.
    move=> ?.
    apply /orP; left.
    apply hext.(em_valid).
    by apply /orP; left.
  + move=> /= p. rewrite hass.(ass_valid) /=.
    move=> ?.
    by apply /orP; left.
  + move=> /= p h1' h2' h3. apply hass.(ass_read_old8). done.
  + move=> /=. by rewrite get_var_eq.
  + move=> /=. rewrite get_var_neq. by rewrite get_var_eq.
    rewrite /vrip0 /vrsp0. move=> []. contradiction.
  + move=> /=. move=> x ? ?.
    have hpmap: wf_pmap (lmap locals1 vnew1) rsp rip Slots Addr Writable Align.
    + apply init_local_map_wf_pmap.
    rewrite get_var_neq. rewrite get_var_neq. done.
    move=> ?; subst x. by have /rsp_in_new /= := hpmap.
    move=> ?; subst x. by have /rip_in_new /= := hpmap.
  + have := init_local_map_wf_rmap. apply.
    simpl.
    move=> i hi.
    rewrite -hass.(ass_read_old8).
    apply hext.(em_read_new). done.
    apply hext.(em_valid). apply /orP. right.
    apply: between_byte hi.
    apply hext.(em_no_overflow).
    apply zbetween_refl.
  + move=> /= w hvalid.
    rewrite -hass.(ass_read_old8) /=.
    apply hext.(em_read_old8). done.
    apply hext.(em_valid). apply /orP. left. done.
  + move=> p hb. apply hext.(em_valid). apply /orP. right. done.
  done.
Qed.

(* It is not clear whether we should use the size of the value [varg1] or the
   size of the corresponding parameter [x] in this definition. Initially,
   we used the latter, but at one point it seemed easier to use the former.
   Since several proofs have been reworked since, this choice could be rethought.
   At least, it works with the current formulation.
*)
Definition disjoint_from_writable_param p opi varg1 varg2 :=
  forall pi p2, opi = Some pi -> varg2 = @Vword Uptr p2 -> pi.(pp_writable) ->
  disjoint_zrange p2 (size_val varg1) p (wsize_size U8).

(* TODO: move *)
Lemma size_fmapM2 eT aT bT cT dT e (f : aT -> bT -> cT -> result eT (aT * dT)) a lb lc a2 ld :
  fmapM2 e f a lb lc = ok (a2, ld) ->
  size lb = size lc /\ size lb = size ld.
Proof.
  elim: lb lc a a2 ld.
  + by move=> [|//] _ _ _ [_ <-].
  move=> b lb ih [//|c lc] a /=.
  t_xrbindP=> _ _ _ _ [_ ld] /ih{ih}ih _ <- /=.
  by lia.
Qed.

(* [disjoint_from_writable_params] correctly captures the notion of being
   disjoint from writable param slots
*)
Lemma disjoint_from_writable_params_param_slots p :
  Forall3 (disjoint_from_writable_param p) sao.(sao_params) vargs1 vargs2 ->
  forall s, Sv.In s Slots_params -> Writable_params s ->
  disjoint_zrange (Addr_params s) (size_slot s) p (wsize_size U8).
Proof.
  move=> hdisj s hin.
  have /in_Slots_params := hin.
  case hpi: get_pi => [[pi [v1 v2]]|//] _.
  have [p2 [? hargp]] := get_pi_wf_arg hpi; subst v2.
  rewrite /Writable_params /Addr_params hpi => hw.
  have [i [hnth1 hnth2 hnth3 hnth4]] := get_pi_nth hpi.
  have hi := nth_not_default hnth2 ltac:(discriminate).
  have := Forall3_nth hdisj None (Vbool true) (Vbool true) hi.
  move: hi; have [-> _] := size_fmapM2 hparams => hi.
  rewrite hnth2 hnth4 => /(_ _ _ refl_equal refl_equal hw).
  apply disjoint_zrange_incl_l.
  apply: zbetween_le.
  rewrite hnth3.
  by apply: get_pi_size_le hpi.
Qed.

(* If p is [disjoint_from_writable_params] and from local variables, it is
   disjoint from all writable params.
*)
Corollary disjoint_from_writable_params_all_slots p :
  Forall3 (disjoint_from_writable_param p) sao.(sao_params) vargs1 vargs2 ->
  disjoint_zrange rsp sao.(sao_size) p (wsize_size U8) ->
  forall s, Sv.In s Slots -> Writable s ->
  disjoint_zrange (Addr s) (size_slot s) p (wsize_size U8).
Proof.
  move=> hdisj1 hdisj2 s hin hw.
  case /in_Slots : hin => [hin|[hin|hin]].
  + by move: hw; rewrite /Writable (pick_slot_globals hin).
  + rewrite /Addr (pick_slot_locals hin).
    by apply (disjoint_zrange_incl_l (zbetween_Addr_locals hin)).
  rewrite /Writable (pick_slot_params hin) in hw.
  rewrite /Addr (pick_slot_params hin).
  by apply (disjoint_from_writable_params_param_slots hdisj1).
Qed.

(*
Lemma init_paramP rmap m0 s1 s2 vnew1' locals1' sao_param param
  vnew2' locals2' rmap2' alloc_param :
  valid_state (lmap locals1' vnew1') rsp rip Slots Addr Writable Align P rmap m0 s1 s2 ->
  init_param mglob stack (vnew1', locals1', rmap) sao_param param = ok (vnew2', locals2', rmap2', alloc_param) ->
  forall s1' varg1 varg2,
  write_var param varg1 s1 = ok s1' ->
  Rin_aux (emem s2) sao_param varg1 varg2 ->
  exists s2',
  write_var alloc_param.2 varg2 s2 = ok s2' /\
  valid_state (lmap locals2' vnew2') rsp rip Slots Addr Writable Align P rmap2' m0 s1' s2'.
Proof.
  move=> hvs.
  rewrite /init_param.
  case: sao_param => [pi|]; last first.
  + move=> [_ _ <- <-]. move=> s1' varg1 varg2 hw ->.
    move: hw.
      rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
      apply: set_varP hvm1=> [v' hv <- | hb hv <-]; rewrite /write_var /set_var hv /= ?hb /=;
        eexists;(split;first by reflexivity). apply valid_state_set_var. done.

Lemma init_paramsP rmap m0 s1 s2 mglob stack disj locals0 sao_params params
disj' locals2 rmap2 alloc_params:
  valid_state rmap m0 s1 s2 ->
  init_params mglob stack disj locals0 rmap sao_params params = ok (disj', locals2, rmap2, alloc_params) ->
  forall s1' vargs vargs',
  write_vars params vargs s1 = ok s1' ->
  Forall3 (Rin_aux (emem s2)) sao_params vargs vargs' ->
  exists s2',
  write_vars (map snd alloc_params) vargs' s2 = ok s2' /\
  valid_state rmap2 m0 s1' s2'.
Proof.
*)
(*
Lemma test0 
vnew1' locals1' rmap1' sao_param (param:var_i) vnew2' locals2' rmap2' alloc_param s1 s2 varg1 varg2 :
  Rin_aux (emem s2) sao_param varg1 varg2 ->
  init_param mglob stack (vnew1', locals1', rmap1') sao_param param =
    ok (vnew2', locals2', rmap2', alloc_param) ->
  forall s1', write_var param varg1 s1 = ok s1' ->
  exists s2',
  write_var alloc_param.2 varg2 s2 = ok s2'.
Proof.
  case: sao_param => [pi|]; last first.
  + move=> -> [_ _ _ <-] /=.
Abort.

(* should we assume sth about valid_state ? or vm_uincl ? *)
Lemma test2 s1 s2 vargs1 vargs2 :
  Forall3 (Rin_aux (emem s2)) sao.(sao_params) vargs1 vargs2 ->
  forall s1', write_vars params vargs1 s1 = ok s1' ->
  exists s2',
  write_vars [seq i.2 | i <- alloc_params] vargs2 s2 = ok s2'.
Proof.
  move=> hin.
  move: hparams s1.
  elim: {vargs1 vargs2} hin params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params.
  + by move=> [|//] ??????? [_ _ _ <-]; exists s2.
  move=> opi varg varg' sao_params vargs vargs' hin1 hin2 ih.
  move=> [//|param params'] vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  t_xrbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  move=> [[[_ _] _]{alloc_params'}alloc_params'] /ih{ih}ih _ <- /=.
  move=> s1 s1'' s1' hs1' /ih ?.
  case: opi hin1 hparam => [pi|]; last first.
  + move=> -> [_ _ _ <-] /=.
(*     rewrite hs1'. *)
(*   alloc_lvalP *)
(*
  case: opi hin1 => [pi|] hin1.
  + 
  case: params => [//|param params'].
  case: opi hin1 => [pi|] hin1.
  rewrite /init_params /=.
  t_xrbindP. 
*)
Admitted.
*)
End LOCAL.

Lemma valid_state_extend_mem pmap rsp Slots Addr Writable Align rmap m0 s1 s2 :
  wf_Slots Slots Addr Writable Align ->
  valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap m0 s1 s2 ->
  extend_mem (emem s1) (emem s2) rip global_data ->
  forall rmap' s1' s2',
  valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap' m0 s1' s2' ->
  validw (emem s1) =2 validw (emem s1') ->
  validw (emem s2) =2 validw (emem s2') ->
  extend_mem (emem s1') (emem s2') rip global_data.
Proof.
  move=> hwf hvs hext rmap' s1' s2' hvs' hvalideq1 hvalideq2.
  case:(hext) => hover halign hold hfresh hvalid hnew.
  split=> //=.
  + by apply (vs_eq_mem (valid_state := hvs')).
  + by move=> p hvalidp; apply hfresh; rewrite hvalideq1.
  + by move=> p; rewrite -hvalideq1 -hvalideq2; apply hvalid.
  move=> i hi.
  have hb: between rip glob_size (rip + wrepr _ i)%R U8.
  + apply: between_byte hi => //.
    by apply zbetween_refl.
  have hvalid0: validw m0 (rip + wrepr _ i)%R U8.
  + by apply (vs_glob_valid (valid_state := hvs)).
  have hnvalid1: ~ validw (emem s1) (rip + wrepr _ i)%R U8.
  + move=> /hfresh.
    by apply zbetween_not_disjoint_zrange.
  have hdisjoint: forall s, Sv.In s Slots -> Writable s ->
    disjoint_zrange (Addr s) (size_slot s) (rip + wrepr U64 i) (wsize_size U8).
  + move=> s hin hw.
    apply disjoint_zrange_sym.
    apply (disjoint_zrange_incl_l hb).
    apply hwf.(wfsl_not_glob) => //.
    by lia.
  rewrite -(vs_unchanged (valid_state:=hvs')) //; last by rewrite -hvalideq1.
  rewrite (vs_unchanged (valid_state:=hvs)) //.
  by apply hnew.
Qed.

Section PROC.

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].

Variable (local_alloc : funname -> stk_alloc_oracle_t).

Hypothesis Halloc_fd : forall fn fd,
  get_fundef P.(p_funcs) fn = Some fd ->
  exists fd', get_fundef P'.(p_funcs) fn = Some fd' /\
              alloc_fd P'.(p_extra) mglob local_alloc (fn, fd) = ok (fn, fd').

(* RAnone -> export function (TODO: rename RAexport?)
   The bound in the first case could be
     sao.(sao_size) + sao.(sao_extra_size) + wsize_size sao.(sao_align) - 1.
*)
Definition enough_size m sao :=
  let sz :=
    if is_RAnone sao.(sao_return_address) then
      sao.(sao_size) + sao.(sao_extra_size) + wsize_size sao.(sao_align) - 1
    else
      round_ws sao.(sao_align) (sao.(sao_size) + sao.(sao_extra_size))
  in
  allocatable_stack m (sao.(sao_max_size) - sz).

(* TODO: wf_sao_max_size should be in a separate record and put in conclusion of Pfun *)
Record wf_sao rsp m sao := {
  wf_sao_size     : enough_size m sao;
  wf_sao_align    : is_align rsp sao.(sao_align);
}.

Lemma stack_stable_wf_sao rsp m1 m2 sao :
  stack_stable m1 m2 ->
  wf_sao rsp m1 sao ->
  wf_sao rsp m2 sao.
Proof.
  move=> hss [hsize halign]; split=> //.
  rewrite /enough_size /allocatable_stack.
  by rewrite -(ss_top_stack hss) -(ss_limit hss).
Qed.

Let Pi_r s1 (i1:instr_r) s2 :=
  forall pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  alloc_i pmap local_alloc sao rmap1 (MkI ii1 i1) = ok (rmap2, MkI ii2 i2) ->
  forall m0 s1', valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip global_data ->
  wf_sao rsp (emem s1') sao ->
  exists s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' /\
              valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2'.

Let Pi s1 (i1:instr) s2 :=
  forall pmap rsp Slots Addr Writable Align rmap1 rmap2 i2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  alloc_i pmap local_alloc sao rmap1 i1 = ok (rmap2, i2) ->
  forall m0 s1', valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip global_data ->
  wf_sao rsp (emem s1') sao ->
  exists s2', sem_I (sCP:= sCP_stack) P' rip s1' i2 s2' /\
              valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2'.

(*
Let Pi_r s1 i1 s2 :=
  forall ii, Pi s1 (MkI ii i1) s2.
*)
(* voire Pi := Pc [:: i], mais sans doute surcout non négligeable *)

Let Pc s1 (c1:cmd) s2 :=
  forall pmap rsp Slots Addr Writable Align rmap1 rmap2 c2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  fmapM (alloc_i pmap local_alloc sao) rmap1 c1 = ok (rmap2, c2) ->
  forall m0 s1', valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip global_data ->
  wf_sao rsp (emem s1') sao ->
  exists s2', sem (sCP:= sCP_stack) P' rip s1' c2 s2' /\
              valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2'.

Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

Definition alloc_ok (SP:sprog) fn m2 :=
  forall fd, get_fundef (p_funcs SP) fn = Some fd ->
  allocatable_stack m2 fd.(f_extra).(sf_stk_max) /\
  (~ is_RAnone fd.(f_extra).(sf_return_address) -> is_align (top_stack m2) fd.(f_extra).(sf_align)).

(* [glob_size] and [rip] were section variables in stack_alloc_proof.v, they
   are section variables in this file too. Can we put everything in the same
   section? Probably not if the file is split.
*)
Definition wf_args m1 m2 fn :=
  Forall3 (wf_arg glob_size rip m1 m2) (local_alloc fn).(sao_params).
Definition wf_results m vargs1 vargs2 fn :=
  Forall3 (wf_result m vargs1 vargs2) (local_alloc fn).(sao_return).

Definition disjoint_from_writable_params fn p :=
  Forall3 (disjoint_from_writable_param p) (local_alloc fn).(sao_params).
Definition mem_unchanged_params fn ms m0 m vargs1 vargs2 :=
  forall p, validw m0 p U8 -> ~ validw ms p U8 -> disjoint_from_writable_params fn p vargs1 vargs2 ->
  read m0 p U8 = read m p U8.

Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) :=
  forall m1' vargs',
    extend_mem m1 m1' rip global_data ->
    wf_args m1 m1' fn vargs vargs' ->
    disjoint_values (local_alloc fn).(sao_params) vargs vargs' ->
    alloc_ok P' fn m1' ->
    exists m2' vres',
      sem_call (sCP := sCP_stack) P' rip m1' fn vargs' m2' vres' /\
      extend_mem m2 m2' rip global_data /\
      wf_results m2' vargs vargs' fn vres vres' /\
      mem_unchanged_params fn m1 m1' m2' vargs vargs'.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s pmap rsp Slots Addr Writable Align rmap1 rmap2 /= c2 hpmap hwf sao [??] m0 s' hv hext hsao;subst rmap1 c2.
  exists s'; split => //; exact: Eskip.
Qed.

Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c hhi Hi hhc Hc pmap rsp Slots Addr Writable Align rmap1 rmap3 c1 hpmap hwf sao /=.
  t_xrbindP => -[rmap2 i'] hi {rmap3} [rmap3 c'] hc /= <- <- m0 s1' hv hext hsao.
  have [s2' [si hv2]]:= Hi _ _ _ _ _ _ _ _ _ hpmap hwf _ hi _ _ hv hext hsao.
  have hsao2 := stack_stable_wf_sao (sem_I_stack_stable_sprog si) hsao.
  have hext2 := valid_state_extend_mem hwf hv hext hv2 (sem_I_validw_stable_uprog hhi) (sem_I_validw_stable_sprog si).
  have [s3' [sc hv3]]:= Hc _ _ _ _ _ _ _ _ _ hpmap hwf _ hc _ _ hv2 hext2 hsao2.
  by exists s3'; split => //; apply: Eseq; [exact: si|exact: sc].
Qed.

Local Lemma HmkI : sem_Ind_mkI P ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi pmap rsp Slots Addr Writable Align rmap1 rmap2 [ii' ir'] hpmap hwf sao ha m0 s1' hv hext hsao.
  by have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := Hi _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ ha _ _ hv hext hsao; exists s2'; split.
Qed.

Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
Proof.
  move=> s1 s1' r tag ty e v v' hv htr hw pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap2' i2'] h /= ??? m0 s2 hvs hext hsao; subst rmap2' ii1 i2'.
  case: ifPn h => [/is_sarrP [n ?]| _ ].
  + subst ty; apply: add_iinfoP.
    move=> halloc.
    have [s2' [hs2' hvs']] := alloc_array_move_initP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap P'_globs hvs hv htr hw halloc.
    by exists s2'.
  t_xrbindP => e'; apply: add_iinfoP => /(alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs) he [rmap2' x'].
  apply: add_iinfoP => hax /= ??; subst rmap2' i2.
  have htyv':= truncate_val_has_type htr.
  have [s2' [/= hw' hvs']]:= alloc_lvalP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap hax hvs htyv' hw.
  exists s2'; split=> //.
  by apply: Eassgn; eauto; rewrite P'_globs; auto.
Qed.

Local Lemma Hopn : sem_Ind_opn P Pi_r.
Proof.
  move=> s1 s2 t o xs es.
  rewrite /sem_sopn; t_xrbindP=> vs va hes hop hw pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP=> -[rmap3 i'] es'; apply: add_iinfoP => he [rmap4 x'];
    apply: add_iinfoP => ha /= [<- <-] <- _ <- m0 s1' hvs hext hsao.
  have [s2' [hw' hvalid']] := alloc_lvalsP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap ha hvs (sopn_toutP hop) hw.
  exists s2'; split=> //.
  by constructor;
    rewrite /sem_sopn P'_globs (alloc_esP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs he hes) /= hop.
Qed.

Local Lemma Hif_true : sem_Ind_if_true P ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] e'; apply: add_iinfoP => he [rmap4 c1'] hc1 [rmap5 c2'] hc2 /= [??]??? m0 s1' hv hext hsao.
  subst rmap3 i' rmap2 ii1 i2.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv he Hse; rewrite -P'_globs => he'.
  have [s2' [Hsem Hvalid']] := Hc _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ hv hext hsao.
  exists s2'; split; first by apply: Eif_true.
  by apply: valid_state_incl Hvalid'; apply incl_merge_l.
Qed.

Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] e'; apply: add_iinfoP => he [rmap4 c1'] hc1 [rmap5 c2'] hc2 /= [??]??? m0 s1' hv hext hsao.
  subst rmap3 i' rmap2 ii1 i2.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv he Hse; rewrite -P'_globs => he'.
  have [s2' [Hsem Hvalid']] := Hc _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ _ hv hext hsao.
  exists s2'; split; first by apply: Eif_false.
  by apply: valid_state_incl Hvalid'; apply incl_merge_r.
Qed.

Lemma loop2P ii check_c2 n rmap rmap' e' c1' c2': 
  loop2 ii check_c2 n rmap = ok (rmap', (e', (c1', c2'))) ->
  exists rmap1 rmap2, incl rmap1 rmap /\ check_c2 rmap1 = ok ((rmap', rmap2), (e', (c1', c2'))) /\ incl rmap1 rmap2.
Proof.
  elim: n rmap => //= n hrec rmap; t_xrbindP => -[[rmap1 rmap2] [e1 [c11 c12]]] hc2 /=; case: ifP.
  + move=> hi [] ????;subst.
    by exists rmap; exists rmap2;split => //; apply incl_refl.
  move=> _ /hrec [rmap3 [rmap4 [h1 [h2 h3]]]]; exists rmap3, rmap4; split => //.
  by apply: (incl_trans h1); apply incl_merge_l.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true P ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c1 e c2 hhi Hc1 Hv hhi2 Hc2 _ Hwhile pmap rsp Slots Addr Writable Align
    rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] [rmap4 [e' [c1' c2']]] /loop2P [rmap5 [rmap6 [hincl1 []]]].
  t_xrbindP => -[rmap7 c11] hc1 /= e1; apply: add_iinfoP => he [rmap8 c22] /= hc2 ????? hincl2 [??]???.
  subst i2 ii1 rmap3 rmap4 i' rmap7 rmap8 e1 c11 c22 => m0 s1' /(valid_state_incl hincl1) hv hext hsao.
  have [s2' [hs1 hv2]]:= Hc1 _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ hv hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv2 he Hv; rewrite -P'_globs => he'.
  have hsao2 := stack_stable_wf_sao (sem_stack_stable_sprog hs1) hsao.
  have hext2 := valid_state_extend_mem hwf hv hext hv2 (sem_validw_stable_uprog hhi) (sem_validw_stable_sprog hs1).
  have [s3' [hs2 /(valid_state_incl hincl2) hv3]]:= Hc2 _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ _ hv2 hext2 hsao2.
  have /= := Hwhile _ _ _ _ _ _ rmap5 rmap2 ii2 ii2 (Cwhile a c1' e' c2') hpmap hwf sao.
  have hsao3 := stack_stable_wf_sao (sem_stack_stable_sprog hs2) hsao2.
  have hext3 := valid_state_extend_mem hwf hv2 hext2 hv3 (sem_validw_stable_uprog hhi2) (sem_validw_stable_sprog hs2).
  rewrite Loop.nbP /= hc1 /= he /= hc2 /= hincl2 /= => /(_ erefl _ _ hv3 hext3 hsao3) [s4'] [hs3 hv4].
  by exists s4';split => //; apply: Ewhile_true; eassumption.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 a c1 e c2 _ Hc1 Hv pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] [rmap4 [e' [c1' c2']]] /loop2P [rmap5 [rmap6 [hincl1 []]]].
  t_xrbindP => -[rmap7 c11] hc1 /= e1; apply: add_iinfoP => he [rmap8 c22] /= hc2 ????? hincl2 [??]???.
  subst i2 ii1 rmap3 rmap4 i' rmap7 rmap8 e1 c11 c22 => m0 s1' /(valid_state_incl hincl1) hv hext hsao.
  have [s2' [hs1 hv2]]:= Hc1 _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ hv hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv2 he Hv; rewrite -P'_globs => he'.
  by exists s2';split => //; apply: Ewhile_false; eassumption.
Qed.

Local Lemma Hfor : sem_Ind_for P ev Pi_r Pfor.
Proof. by []. Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by []. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons P ev Pc Pfor.
Proof. by []. Qed.

Lemma Forall3_size A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  Forall3 R l1 l2 l3 ->
  size l1 = size l2 /\ size l1 = size l3.
Proof.
  elim {l1 l2 l3} => //.
  by move=> a b c l1 l2 l3 _ _ [??]; split=> /=; congruence.
Qed.

Lemma mapM2_Forall3 A B E R (e : E) (f : A -> B -> result E R) la lb lr :
  mapM2 e f la lb = ok lr ->
  Forall3 (fun a b r => f a b = ok r) la lb lr.
Proof.
  elim: la lb lr.
  + by move=> [|//] [|//] _; constructor.
  move=> a la ih [//|b lb] /=.
  t_xrbindP=> _ r hf lr /ih{ih}ih <-.
  by constructor.
Qed.

(* TODO: is already somewhere else *)
Lemma mapM2_truncate_val_value_uincl tyin vargs1 vargs1' :
  mapM2 ErrType truncate_val tyin vargs1 = ok vargs1' ->
  List.Forall2 value_uincl vargs1' vargs1.
Proof.
  move=> htr.
  have {htr} := mapM2_Forall3 htr.
  elim {vargs1 vargs1'} => //.
  move=> _ v1 v1' _ vargs1 vargs1' /truncate_value_uincl huincl _ ih.
  by constructor.
Qed.

Lemma get_var_bytes_set_clear_bytes rv sr ofs len r y :
  get_var_bytes (set_clear_bytes rv sr ofs len) r y =
    let bytes := get_var_bytes rv r y in
    if sr.(sr_region) != r then bytes
    else
      let i := interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs len) in
      ByteSet.remove bytes i.
Proof.
  rewrite /set_clear_bytes /get_var_bytes.
  rewrite get_bytes_map_setP.
  case: eqP => [->|] //=.
  by rewrite get_bytes_clear.
Qed.

Lemma set_clear_set_bytes rv x sr ofs len rv2 rv3 rv4 :
  set_clear_bytes rv sr (Some ofs) len = rv2 ->
  set_pure_bytes rv2 x sr (Some ofs) len = rv3 ->
  set_pure_bytes rv x sr (Some ofs) len = rv4 ->
  forall y r, ByteSet.mem (get_var_bytes rv3 r y) =1 ByteSet.mem (get_var_bytes rv4 r y).
Proof.
  move=> h1 h2 h3 y r.
  rewrite -h2 -h3.
  rewrite !get_var_bytes_set_pure_bytes.
  rewrite -h1.
  rewrite get_var_bytes_set_clear_bytes.
  case: eqP => heqr //=.
  case: eqP => heq.
  + move=> bytes.
    apply /idP/idP.
    + move=> /ByteSet.memP H. apply /ByteSet.memP.
      move=> i /H{H}. rewrite !ByteSet.addE.
      rewrite ByteSet.removeE.
      move=> /orP [H|H].
      + apply /orP. left. done.
      move /andP : H => [? _].
      apply /orP. right. done.
    move=> /ByteSet.memP H. apply /ByteSet.memP.
    move=> i /H{H}. rewrite !ByteSet.addE.
    rewrite ByteSet.removeE.
    move=> /orP [H|H].
    + apply /orP. left. done.
    case heq2: I.memi.
    + done.
    simpl. rewrite H. done.
  move=> bytes.
  apply /idP/idP.
  move=> /ByteSet.memP H.
  apply /ByteSet.memP.
  move=> i /H.
  rewrite !ByteSet.removeE.
  rewrite -andbA.
  rewrite Bool.andb_diag. done.
  move=> /ByteSet.memP H.
  apply /ByteSet.memP.
  move=> i /H.
  rewrite !ByteSet.removeE.
  rewrite -andbA.
  rewrite Bool.andb_diag. done.
Qed.

Lemma Forall_nth A (R : A -> Prop) l :
  List.Forall R l ->
  forall d i, (i < size l)%nat -> R (nth d l i).
Proof.
  elim {l} => //.
  move=> a l h _ ih d [|i].
  + move=> _ /=. done.
  apply ih.
Qed.

Lemma nth_Forall A (R : A -> Prop) l d :
  (forall i, (i < size l)%nat -> R (nth d l i)) ->
  List.Forall R l.
Proof.
  elim: l => //.
  move=> a l ih h.
  constructor.
  + by apply (h 0%nat).
  apply ih.
  move=> i.
  apply (h i.+1).
Qed.

Lemma nth_Forall2 A B (R : A -> B -> Prop) l1 l2 a b:
  size l1 = size l2 ->
  (forall i, (i < size l1)%nat -> R (nth a l1 i) (nth b l2 i)) ->
  List.Forall2 R l1 l2.
Proof.
  elim: l1 l2.
  + move=> [|//] _ _; constructor.
  move=> a0 l1 ih [//|b0 l2] [hsize] h.
  constructor.
  + by apply (h 0%nat).
  apply ih => //.
  move=> i. apply (h i.+1).
Qed.

Lemma alloc_fd_max_size_ge0 pex fn fd fd' :
  alloc_fd pex mglob local_alloc (fn, fd) = ok (fn, fd') ->
  0 <= (local_alloc fn).(sao_max_size).
Proof.
  rewrite /alloc_fd /=.
  t_xrbindP=> ?? hlayout [[??]?] hlocal_map.
  t_xrbindP=> -[[[??]?]?] hparams.
  t_xrbindP=> _ /assertP /ZleP hextra _ /assertP /ZleP hmax _ _ _ _.
  have hsize := init_stack_layout_size_ge0 hlayout.
  case: is_RAnone hmax.
  + have := wsize_size_pos (local_alloc fn).(sao_align).
    by lia.
  have := round_ws_range (local_alloc fn).(sao_align) ((local_alloc fn).(sao_size) + (local_alloc fn).(sao_extra_size)).
  by lia.
Qed.

(* TODO: move *)
Lemma disjointi_incl_l b1 b2 i :
  ByteSet.subset b1 b2 ->
  disjointi b2 i ->
  disjointi b1 i.
Proof.
  move=> /ByteSet.subsetP hsubset /disjointiP hdisj.
  by apply /disjointiP; eauto.
Qed.

(* TODO: move *)
Lemma disjointi_incl_r b i1 i2 :
  I.subset i1 i2 ->
  disjointi b i2 ->
  disjointi b i1.
Proof.
  move=> /subset_memi hsubset /disjointiP hdisj.
  apply /disjointiP => n hmem hmemi.
  apply (hdisj _ hmem).
  by apply hsubset.
Qed.

(* TODO: move *)
Lemma disjointi_set_clear rmap sr ofs len x :
  disjointi (get_var_bytes (set_clear_pure rmap sr ofs len) sr.(sr_region) x) (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs len)).
Proof.
  rewrite get_var_bytes_set_clear_bytes eq_refl /=.
  apply /disjointiP => n.
  by rewrite ByteSet.removeE => /andP [_ /negP ?].
Qed.

(* TODO: vundef_type should maybe be changed now is_sarr t = false is an argument of Vundef *)
Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
Proof.
  move=> s1 m1 s1' ii rs fn args vargs1 vres1 hvargs1 hsem1 Hf hs1'.
  move=> pmap rsp Slots Addr Writable Align rmap0 rmap2 ii1 ii2 i2 hpmap hwfsl sao /=.
  t_xrbindP=> -[rmap2' i2']; apply: add_iinfoP => /= halloc ? {ii1 ii2} _ ? m0 s2 hvs hext hsao; subst rmap2' i2'.
  move: halloc; rewrite /alloc_call.
  t_xrbindP=> -[rmap1 es] hcargs.
  t_xrbindP=> -[{rmap2}rmap2 rs2] hcres _ /assertP /ZleP hsize _ /assertP hle /= <- <-.

  (* evaluation of the arguments *)
  have [vargs2 [hvargs2 hargs hdisj haddr hclear]] :=
    alloc_call_argsP hwfsl.(wfsl_no_overflow) hwfsl.(wfsl_disjoint) hwfsl.(wfsl_align) hwfsl.(wfsl_not_glob) hpmap hvs hcargs hvargs1.

  (* function call *)
  have [fd1 hfd1]: exists fd, get_fundef P.(p_funcs) fn = Some fd.
  + have /sem_callE [fd1 [hfd1 _]] := hsem1.
    by exists fd1.
  have [fd2 [hfd2 halloc]] := Halloc_fd hfd1.
  have hmax := alloc_fd_max_size_ge0 halloc.
  move: halloc hfd2; rewrite /alloc_fd.
  t_xrbindP=> {fd2}fd2 _ <- hfd2.
  have halloc_ok: alloc_ok P' fn (emem s2).
  + rewrite /alloc_ok hfd2 => _ [<-] /=.
    split.
    + rewrite /allocatable_stack.
      move: hsao.(wf_sao_size); rewrite /enough_size /allocatable_stack.
      by lia.
    move=> _.
    have := hsao.(wf_sao_align).
    have /vs_top_stack -> := hvs.
    by apply is_align_m.
  have [m2 [vres2 [hsem2 [hext' [hresults hunch]]]]] := Hf _ _ hext hargs hdisj halloc_ok.

  (* after function call, we have [valid_state] for [rmap1] where all writable arguments
     have been cleared.
  *)
  have hvs': valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap1 m0 (with_mem s1 m1) (with_mem s2 m2).
  + have [hcargsx _] := alloc_call_argsE hcargs.
    set l :=
      seq.pmap (fun '(bsr, ty) =>
        match bsr with
        | Some (true, sr) => Some (sub_region_at_ofs sr (Some 0) (size_of ty), ty)
        | _               => None
        end) (zip (map fst es) (map type_of_val vargs1)).
    have hlin: forall sr ty, (sr, ty) \in l <->
      exists k sr', [/\ ty = type_of_val (nth (Vbool true) vargs1 k),
                        nth None (map fst es) k = Some (true, sr') &
                        sr = sub_region_at_ofs sr' (Some 0) (size_of ty)].
    + move=> sr ty.
      rewrite /l mem_pmap -(rwP mapP) /=.
      have heqsize: size (map fst es) = size (map type_of_val vargs1).
      + rewrite 2!size_map.
        have [_ <-] := size_fmapM2 hcargsx.
        by have [? _] := Forall3_size hargs.
      split.
      + move=> [[[[[|//] sr']|//] ty'] hin [??]]; subst sr ty'.
        move: hin.
        move=> /nthP -/(_ (None, sbool)).
        rewrite size1_zip heqsize // => -[k hk].
        rewrite (nth_zip _ _ _ heqsize) => -[hsr' <-].
        exists k, sr'; split=> //.
        rewrite (nth_map (Vbool true)) //.
        by move: hk; rewrite size_map.
      move=> [k [sr' [-> hsr' ->]]].
      exists (Some (true, sr'), type_of_val (nth (Vbool true) vargs1 k)) => //.
      apply /(nthP (None, sbool)).
      exists k.
      + rewrite size1_zip -?heqsize //.
        apply (nth_not_default hsr' ltac:(discriminate)).
      rewrite (nth_zip _ _ _ heqsize) hsr' (nth_map (Vbool true)) //.
      move: heqsize; rewrite (size_map _ vargs1) => <-.
      apply (nth_not_default hsr' ltac:(discriminate)).

    have hvs' := valid_state_incl (alloc_call_args_aux_incl hcargsx) hvs.
    apply (valid_state_holed_rmap hwfsl.(wfsl_no_overflow) hwfsl.(wfsl_disjoint) hpmap hvs'
             (sem_call_validw_stable_uprog hsem1) (sem_call_stack_stable_sprog hsem2)
             (sem_call_validw_stable_sprog hsem2) hext'.(em_read_old8) (l:=l)).
    + apply List.Forall_forall => -[sr ty] /InP.
      rewrite hlin => -[k [sr' [-> hsr' ->]]] /=.
      split.
      + have [_ hwf'] := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ _ hsr'.
        apply (sub_region_at_ofs_wf hwf' (ofs:=Some 0)).
        by move=> _ [<-]; lia.
      by apply (Forall_nth (alloc_call_args_aux_writable hcargsx) None (nth_not_default hsr' ltac:(discriminate)) _ hsr').
    + move=> p hvalid1 hvalid2 hdisj'.
      symmetry; apply hunch => //.
      apply (nth_Forall3 None (Vbool true) (Vbool true)).
      + by have [? _] := Forall3_size hargs.
      + by have [_ ?] := Forall3_size hargs.
      move=> i hi pi p2 hpi hp2 hw.
      have [sr hsr] := Forall2_nth (alloc_call_args_aux_not_None hcargsx) None None hi _ hpi.
      rewrite hw in hsr.
      have := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr ltac:(discriminate)) _ _ hsr.
      rewrite hp2 => -[[?] hwf']; subst p2.
      have {hw}hw := Forall_nth (alloc_call_args_aux_writable hcargsx) None (nth_not_default hsr ltac:(discriminate)) _ hsr.
      have /List.Forall_forall -/(_ (sub_region_at_ofs sr (Some 0) (size_val (nth (Vbool true) vargs1 i)), type_of_val (nth (Vbool true) vargs1 i))) := hdisj'.
      rewrite -sub_region_addr_offset wrepr0 GRing.addr0.
      apply.
      apply /InP /hlin.
      by exists i, sr.
    apply List.Forall_forall => -[sr ty] /InP /hlin [i [sr' [-> hsr' ->]]] x.
    have hincl := Forall2_nth hclear None (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ hsr'.
    apply (disjointi_incl_l (incl_get_var_bytes _ _ hincl)) => /=.
    by apply disjointi_set_clear.

  (* writing of the returned values *)
  have [s2' [hs2' hvs'']] := alloc_call_resP hwfsl.(wfsl_no_overflow) hwfsl.(wfsl_disjoint) hpmap hvs' hcres haddr hresults hs1'.

  exists s2'; split=> //.
  by econstructor; try eassumption; rewrite P'_globs.
Qed.

Lemma add_err_funP A (a:A) (e:cexec A) P0 fn :
  (e = ok a -> P0) -> add_err_fun fn e = ok a -> P0.
Proof.
  case: e => //= a' h [?]; subst a'.
  by apply h.
Qed.

(* Not sure at all if this is the right way to do the proof. *)
Lemma wbit_subword (ws ws' : wsize) i (w : word ws) k :
  wbit_n (word.subword i ws' w) k = (k < ws')%nat && wbit_n w (k + i).
Proof.
  rewrite /wbit_n.
  case: ltP.
  + move=> /ltP hlt.
    by rewrite word.subwordE word.wbit_t2wE (nth_map 0%R) ?size_enum_ord // nth_enum_ord.
  rewrite /nat_of_wsize => hle.
  rewrite word.wbit_word_ovf //.
  by apply /ltP; lia.
Qed.

Lemma zero_extend_wread8 (ws ws' : wsize) (w : word ws) :
  (ws' <= ws)%CMP ->
  forall off,
  0 <= off < wsize_size ws' ->
  LE.wread8 (zero_extend ws' w) off = LE.wread8 w off.
Proof.
  move=> /wsize_size_le hle off hoff.
  rewrite /LE.wread8 /LE.encode /split_vec.
  have hmod: forall (ws:wsize), ws %% U8 = 0%nat.
  + by move=> [].
  have hdiv: forall (ws:wsize), ws %/ U8 = Z.to_nat (wsize_size ws).
  + by move=> [].
  have hlt: (Z.to_nat off < Z.to_nat (wsize_size ws))%nat.
  + by apply /ltP /Z2Nat.inj_lt; lia.
  have hlt': (Z.to_nat off < Z.to_nat (wsize_size ws'))%nat.
  + by apply /ltP /Z2Nat.inj_lt; lia.
  rewrite !hmod !addn0.
  rewrite !(nth_map 0%nat) ?size_iota ?hdiv // !nth_iota // !add0n.
  apply /eqP/eq_from_wbit_n => i.
  rewrite !wbit_subword; f_equal.
  rewrite wbit_zero_extend.
  have -> //: (i + Z.to_nat off * U8 <= wsize_size_minus_1 ws')%nat.
  rewrite -ltnS -/(nat_of_wsize ws').
  apply /ltP.
  have := ltn_ord i; rewrite -/(nat_of_wsize _) => /ltP hi.
  have /ltP ? := hlt'.
  have <-: (Z.to_nat (wsize_size ws') * U8 = ws')%nat.
  + by case: (ws').
  by rewrite -!multE -!plusE; nia.
Qed.

(* Actually, I think we could have proved something only for arrays, since we
   use this result when the target value is a pointer, in which case the source
   value is an array. But it is not clear whether we know that the source value
   is an array at the point where we need this lemma. And now that we have this
   more general version...
*)
Lemma value_uincl_get_val_byte v1 v2 :
  value_uincl v1 v2 ->
  forall off w,
    get_val_byte v1 off = ok w ->
    get_val_byte v2 off = ok w.
Proof.
  move=> /value_uinclE; case: v1 => //=.
  + move=> len a [len2 [a2 -> [_ hincl]]].
    by apply hincl.
  + move=> ws w [ws2 [w2 [-> /andP [hle /eqP ->]]]].
    move=> off w' /=.
    case: ifP => //; rewrite !zify => hoff.
    have hle' := wsize_size_le hle.
    case: ifPn => [_|]; last by rewrite !zify; lia.
    move=> <-; f_equal; symmetry.
    by apply zero_extend_wread8.
Qed.

(* We don't need the hypothesis that [varg1] and [varg1'] are arrays, since
   we have the powerful [value_uincl_get_val_byte]. If we had a weaker version,
   we should probably add this hypothesis.
*)
Lemma value_uincl_wf_arg_pointer m1 m2 pi varg1 varg1' p :
  value_uincl varg1' varg1 ->
  wf_arg_pointer glob_size rip m1 m2 pi varg1 p ->
  wf_arg_pointer glob_size rip m1 m2 pi varg1' p.
Proof.
  move=> huincl [halign hover hvalid hfresh hwnglob hread].
  have hle := size_of_le (value_uincl_subtype huincl).
  split=> //.
  + by apply (no_overflow_incl (zbetween_le _ hle)).
  + move=> w hb; apply hvalid.
    apply: zbetween_trans hb.
    by apply zbetween_le.
  + move=> w /hfresh.
    apply disjoint_zrange_incl_l.
    by apply zbetween_le.
  + move=> hw hgsize.
    apply: disjoint_zrange_incl_r (hwnglob hw hgsize).
    by apply zbetween_le.
  by move=> off w /(value_uincl_get_val_byte huincl) /hread.
Qed.

Lemma mapM2_truncate_val_wf_args m1 m2 fn vargs1 vargs2 :
  wf_args m1 m2 fn vargs1 vargs2 ->
  forall tyin vargs1',
  mapM2 ErrType truncate_val tyin vargs1 = ok vargs1' ->
  exists vargs2',
    mapM2 ErrType truncate_val
      (map2 (fun o ty =>
        match o with
        | Some _ => sword64
        | None => ty
        end) (sao_params (local_alloc fn)) tyin) vargs2 = ok vargs2' /\
    wf_args m1 m2 fn vargs1' vargs2'.
Proof.
  rewrite /wf_args.
  elim {vargs1 vargs2}.
  + move=> [|//] /= _ [<-].
    eexists; split; first by reflexivity.
    by constructor.
  move=> opi varg1 varg2 sao_params vargs1 vargs2 harg _ ih [//|ty tyin] /=.
  t_xrbindP=> _ varg1' hvarg1' vargs1' /ih{ih}[vargs2' [htr hargs]] <-.
  rewrite htr /=.
  case: opi harg => [pi|].
  + move=> [p [-> hargp]].
    rewrite /= zero_extend_u.
    eexists; split; first by reflexivity.
    constructor=> //.
    exists p; split=> //.
    apply: value_uincl_wf_arg_pointer hargp.
    by apply (truncate_value_uincl hvarg1').
  move=> /= ->.
  rewrite hvarg1' /=.
  eexists; split; first by reflexivity.
  by constructor.
Qed.

(* If the parameter is a reg ptr, [varg2] is a pointer, and is equal to [varg2']. *)
Lemma mapM2_truncate_val_ptr_eq m1 m2 fn vargs1 vargs2 :
  wf_args m1 m2 fn vargs1 vargs2 ->
  forall tyin vargs2',
  mapM2 ErrType truncate_val
    (map2 (fun o ty =>
          match o with
          | Some _ => sword64
          | None => ty
          end) (sao_params (local_alloc fn)) tyin) vargs2 = ok vargs2' ->
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2'.
Proof.
  elim {vargs1 vargs2}.
  + by move=> /= _ _ [<-]; constructor.
  move=> opi varg1 varg2 sao_params vargs1 vargs2 harg _ ih [//|ty tyin] /=.
  t_xrbindP=> _ varg2' hvarg2' vargs2' /ih{ih}ih <-.
  constructor=> //.
  case: opi harg hvarg2' => [pi|//] [p [-> ?]].
  rewrite /truncate_val /= zero_extend_u.
  by move=> [<-].
Qed.

Lemma value_uincl_disjoint_values m1 m2 fn vargs1 vargs2 :
  wf_args m1 m2 fn vargs1 vargs2 ->
  disjoint_values (local_alloc fn).(sao_params) vargs1 vargs2 ->
  forall vargs1' vargs2',
  List.Forall2 value_uincl vargs1' vargs1 ->
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2' ->
  disjoint_values (local_alloc fn).(sao_params) vargs1' vargs2'.
Proof.
  move=> hargs hdisj vargs1' vargs2' hincl hptreq.
  move=> i1 pi1 w1 i2 pi2 w2 hpi1 hw1 hpi2 hw2 hneq hw.
  have := Forall3_nth hptreq None (Vbool true) (Vbool true).
  move=> /dup[].
  move=> /(_ _ (nth_not_default hpi1 ltac:(discriminate))); rewrite hpi1 => /(_ ltac:(discriminate)); rewrite hw1 => hw1'.
  move=> /(_ _ (nth_not_default hpi2 ltac:(discriminate))); rewrite hpi2 => /(_ ltac:(discriminate)); rewrite hw2 => hw2'.
  have := hdisj _ _ _ _ _ _ hpi1 hw1' hpi2 hw2' hneq hw.
  have := Forall2_nth hincl (Vbool true) (Vbool true).
  have -> := Forall2_size hincl.
  have [<- _] := Forall3_size hargs.
  move=> /dup[].
  move=> /(_ _ (nth_not_default hpi1 ltac:(discriminate))) /value_uincl_subtype /size_of_le hle1.
  move=> /(_ _ (nth_not_default hpi2 ltac:(discriminate))) /value_uincl_subtype /size_of_le hle2.
  by apply disjoint_zrange_incl; apply zbetween_le.
Qed.

Lemma value_uincl_wf_result_pointer m vargs1 vargs2 i vr1 vr1' p :
  value_uincl vr1' vr1 ->
  wf_result_pointer m vargs1 vargs2 i vr1 p ->
  wf_result_pointer m vargs1 vargs2 i vr1' p.
Proof.
  move=> huincl [hargs hsub hread].
  have hsub' := value_uincl_subtype huincl.
  split=> //.
  + by apply: subtype_trans hsub.
  by move=> off w /(value_uincl_get_val_byte huincl) /hread.
Qed.

(* TODO: are vargs1 and vargs2 the same in hyp and concl ?
   Should they be replaced in concl with [mapM2 truncate_val vargs1]
   and [mapM2 truncate_val (map2 ... ...) vargs1]
*)
Lemma mapM2_truncate_val_wf_results m vargs1 vargs2 fn vres1 vres2 :
  wf_results m vargs1 vargs2 fn vres1 vres2 ->
  forall tyout vres1',
  mapM2 ErrType truncate_val tyout vres1 = ok vres1' ->
  exists vres2',
    mapM2 ErrType truncate_val
      (map2 (fun o ty =>
        match o with
        | Some _ => sword64
        | None => ty
        end) (sao_return (local_alloc fn)) tyout) vres2 = ok vres2' /\
    wf_results m vargs1 vargs2 fn vres1' vres2'.
Proof.
  rewrite /wf_results.
  elim {vres1 vres2}.
  + move=> [|//] /= _ [<-].
    eexists; split; first by reflexivity.
    by constructor.
  move=> i vr1 vr2 sao_returns vres1 vres2 hresult _ ih [//|ty tyout] /=.
  t_xrbindP=> _ vr1' hvr1' vres1' /ih{ih}[vres2' [htr hresults]] <-.
  rewrite htr /=.
  case: i hresult => [i|].
  + move=> [p [-> hresultp]].
    rewrite /= zero_extend_u.
    eexists; split; first by reflexivity.
    constructor=> //.
    eexists; split; first by reflexivity.
    apply: value_uincl_wf_result_pointer hresultp.
    by apply (truncate_value_uincl hvr1').
  move=> /= ->.
  rewrite hvr1' /=.
  eexists; split; first by reflexivity.
  by constructor.
Qed.

Hypothesis rip_rsp_neq : P'.(p_extra).(sp_rip) <> x86_variables.string_of_register RSP.

(* TODO: probably notF is not the cleanest way to make this proof *)
(* TODO: stack_region_is_free -> use top_stack *)
Lemma ass_fresh_alt m1 ws sz sz' m2 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  forall p, validw m1 p U8 ->
  ~ pointer_range (top_stack m2) (top_stack m1) p.
Proof.
  move=> hass p hvalid.
  rewrite /pointer_range !zify => -[hp1 hp2].
  have := hass.(ass_fresh) hvalid; rewrite wsize8 => hfresh.
  have habove := hass.(ass_above_limit).
  assert (hfree := stack_region_is_free (m:=m1) (p:=p)).
  rewrite hvalid -/(top_stack _) /= in hfree.
  apply notF; apply hfree.
  by lia.
Qed.

(* This lemma is probably useless, but nonetheless true. *)
(* We know that we are not valid between top_stack and stack_limit, thus this
   lemma.
   Maybe we could just unfold top_stack and use ass_frames ? Same idea for the
   previous lemma ?
*)
Lemma ass_fresh_stronger m1 ws sz sz' m2 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  0 <= sz ->
  forall p, validw m1 p U8 ->
  wunsigned p + wsize_size U8 <= wunsigned (stack_limit m2)
  \/ wunsigned (top_stack m2) + sz <= wunsigned p.
Proof.
  move=> hass hsz p hvalid.
  have := hass.(ass_fresh) hvalid; rewrite wsize8.
  case=> hfresh; last by right.
  left.
  have habove := hass.(ass_above_limit).
  assert (hfree := stack_region_is_free (m:=m1) (p:=p)).
  rewrite hvalid -/(top_stack _) /= in hfree.
  apply Znot_gt_le => ?.
  apply notF; apply hfree.
  rewrite -hass.(ass_limit).
  by lia.
Qed.

Lemma test_ m1 ws sz sz' m2 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  wunsigned (stack_limit m1) <= wunsigned (top_stack m2) /\
  wunsigned (top_stack m2) + sz + sz' <= wunsigned (top_stack m1).
Proof.
  move=> hass.
  rewrite /(top_stack m2) hass.(ass_frames) /=.
  split; last first.
  + rewrite /top_stack_after_alloc.
    assert (bla := align_word_range ws (top_stack m1 + wrepr _ (-(sz + sz')))%R).
    move: bla => [h1 h2].
    move: h2. rewrite wunsigned_add. lia.
Abort.

Lemma test2_ m1 ws sz sz' m2 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  wunsigned (top_stack m1) <= wunsigned (top_stack m2) + sz + sz' + wsize_size ws - 1.
Proof.
  move=> hass.
  rewrite /(top_stack m2) hass.(ass_frames) /=.
  rewrite /top_stack_after_alloc.
  assert (bla := align_word_range ws (top_stack m1 + wrepr _ (-(sz + sz')))%R).
  move: bla => [h1 h2].
  move: h1. rewrite wunsigned_add. lia.
Abort.

(* Can we deduce this part of ass_above_limit from other clauses of alloc_stack_spec ? *)
(* not obvious if we don't have any info on [sz] not [sz'] *)
Lemma ass_above_limit' m1 ws sz sz' m2 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  wunsigned (top_stack m2) + sz <= wunsigned (top_stack m1).
Proof.
  move=> hass.
  rewrite {1}/top_stack hass.(ass_frames) /= /top_stack_after_alloc.
  assert (HH := align_word_range ws (top_stack m1 + wrepr _ (- (sz + sz')))%R).
  case: HH => _ H.
  move: H.
  rewrite wunsigned_add_if.
Abort.

Lemma ass_no_overflow m1 ws sz sz' m2 :
  alloc_stack_spec m1 ws sz sz' m2 -> no_overflow (top_stack m2) sz.
Proof.
  move=> hass.
  rewrite /no_overflow zify.
  have := hass.(ass_above_limit).
  assert (hover := wunsigned_range (top_stack m1)).
  by lia.
Qed.

(* TODO: should be written
   Forall2 (fun x v2 => is_sarr x.(vtype) -> size_slot x <= size_val v) l params ????
   But maybe more complex to use?
*)
Lemma write_vars_subtype A (l:seq (option A)) params :
  List.Forall2 (fun o (x:var_i) => o <> None -> is_sarr x.(vtype)) l params ->
  forall vargs1 s1 s2,
  write_vars params vargs1 s1 = ok s2 ->
  Forall3 (fun o (x:var_i) v => o <> None -> subtype x.(vtype) (type_of_val v)) l params vargs1.
Proof.
  elim {l params}.
  + by move=> [|//] _ _ _; constructor.
  move=> o x l params harr _ ih [//|varg1 vargs1] /=.
  t_xrbindP=> s1 s3 s2 hw /ih{ih}ih.
  constructor=> //.
  move=> /harr /is_sarrP [n hty].
  move: hw; rewrite /write_var.
  t_xrbindP=> vm1 hvm1 _.
  apply: set_varP hvm1; last by rewrite {1}hty.
  move=> t h _; move: t h; rewrite hty /=.
  by move=> _ /to_arrI [n' [_ [-> /WArray.cast_len /ZleP]]] /=.
Qed.

Lemma alloc_stack_spec_wf_args m1 m2 fn vargs1 vargs2 ws sz sz' m3 :
  wf_args m1 m2 fn vargs1 vargs2 ->
  alloc_stack_spec m2 ws sz sz' m3 ->
  wf_args m1 m3 fn vargs1 vargs2.
Proof.
  move=> hargs hass.
  apply: Forall3_impl hargs.
  move=> [pi|//] varg1 _ [p [-> hargp]].
  eexists; split; first by reflexivity.
  case: hargp => halign hover hvalid hfresh hwnglob hread.
  split=> //.
  + by move=> ??; rewrite hass.(ass_valid) hvalid.
  move=> off w /dup[] /get_val_byte_bound hoff /hread.
  rewrite hass.(ass_read_old8) //.
  apply hvalid.
  apply: between_byte hoff => //.
  by apply zbetween_refl.
Qed.

Lemma alloc_stack_spec_extend_mem m1 m2 ws sz sz' m3 :
  extend_mem m1 m2 rip global_data ->
  alloc_stack_spec m2 ws sz sz' m3 ->
  extend_mem m1 m3 rip global_data.
Proof.
  move=> hext hass.
  case:(hext) => hover halign hold hfresh hvalid hnew.
  split=> //.
  + move=> ??; rewrite hold //.
    apply hass.(ass_read_old8).
    by apply hvalid; apply /orP; left.
  + move=> ? /hvalid.
    by rewrite hass.(ass_valid) => ->.
  move=> i hi; rewrite -hnew //.
  symmetry.
  apply hass.(ass_read_old8).
  apply hvalid; apply /orP; right.
  apply: between_byte hi => //.
  by apply zbetween_refl.
Qed.

Lemma free_stack_spec_extend_mem m1 m2 m3 :
  extend_mem m1 m2 rip global_data ->
  free_stack_spec m2 m3 ->
  (forall p, validw m1 p U8 || between rip (Z.of_nat (size global_data)) p U8 -> validw m3 p U8) ->
  extend_mem m1 m3 rip global_data.
Proof.
  move=> hext hfss hincl.
  case:(hext) => hover halign hold hfresh hvalid hnew.
  split=> //.
  + move=> p ?.
    rewrite -hfss.(fss_read_old8); first by apply hold.
    apply hincl.
    by apply /orP; left.
  move=> i hi.
  rewrite -hfss.(fss_read_old8); first by apply hnew.
  apply hincl.
  apply /orP; right.
  apply: between_byte hi => //.
  by apply zbetween_refl.
Qed.

Lemma round_wsE ws sz : round_ws ws sz =
  if sz mod wsize_size ws == 0 then sz else sz + wsize_size ws - sz mod wsize_size ws.
Proof.
  have ws_pos : wsize_size ws ≠ 0 by case: ws.
  rewrite /round_ws.
  elim_div => /(_ ws_pos) [] ->{sz} D.
  case: eqP => ?.
  - reflexivity.
  lia.
Qed.

Lemma wunsigned_add_mod_wsize_size ws ws' (w1 w2 : word ws) :
  wunsigned (w1 + w2) mod wsize_size ws' = (wunsigned w1 + wunsigned w2) mod wsize_size ws'.
Proof.
  rewrite wunsigned_add_if.
  case: ZltP => // _.
  rewrite Zminus_mod.
  rewrite (Znumtheory.Zdivide_mod _ _ (wsize_size_div_wbase _ _)) Z.sub_0_r.
  by rewrite Zmod_mod.
Qed.

Lemma wunsigned_sub_mod_wsize_size ws ws' (w1 w2 : word ws) :
  wunsigned (w1 - w2) mod wsize_size ws' = (wunsigned w1 - wunsigned w2) mod wsize_size ws'.
Proof.
  rewrite wunsigned_sub_if.
  case: ZleP => // _.
  rewrite -Z.add_sub_assoc Zplus_mod.
  rewrite (Znumtheory.Zdivide_mod _ _ (wsize_size_div_wbase _ _)) Z.add_0_l.
  by rewrite Zmod_mod.
Qed.

(* It can be proved! No need to be an axiom in Memory!
   TODO: move
*)
Lemma top_stack_after_aligned_alloc p ws sz :
  is_align p ws ->
  top_stack_after_alloc p ws sz = (p + wrepr Uptr (- round_ws ws sz))%R.
Proof.
  rewrite /is_align p_to_zE => /eqP hal.
  rewrite round_wsE.
  rewrite /top_stack_after_alloc.
  apply wunsigned_inj.
  rewrite align_wordE.
  rewrite !wrepr_opp.

  have h: wunsigned (p - wrepr U64 sz) mod wsize_size ws = - (sz mod wsize_size ws) mod wsize_size ws.
  + by rewrite wunsigned_sub_mod_wsize_size Zminus_mod hal Z.sub_0_l wunsigned_repr mod_wsize_size.

  case: eqP => hsz.
  + by rewrite h Z.mod_opp_l_z // ?Zmod_mod // Z.sub_0_r.
  rewrite Z.mod_opp_l_nz // Zmod_mod // in h.
  rewrite -Z.add_sub_assoc -h.
  rewrite wrepr_add -{1}[p in RHS](GRing.subrK (wrepr U64 sz)) GRing.addrKA.
  rewrite [RHS]wunsigned_sub //.
  have := Z.mod_le _ _ (ge0_wunsigned (p - wrepr U64 sz)) (wsize_size_pos ws).
  have := wunsigned_range (p - wrepr U64 sz).
  have := Z_mod_lt (wunsigned (p - wrepr U64 sz)) (wsize_size ws) ltac:(done).
  by lia.
Qed.

(* no need to be only in memory_example ! *)
(* TODO: move *)
Lemma top_stack_after_alloc_bounded p ws sz :
  0 <= sz ∧ sz <= wunsigned p ->
  wunsigned p - wunsigned (top_stack_after_alloc p ws sz) <= sz + wsize_size ws - 1.
Proof.
  move=> hsz.
  rewrite /top_stack_after_alloc.
  have := align_word_range ws (p + wrepr _ (- sz)).
  rewrite wunsigned_add; first by lia.
  by have := wunsigned_range p; lia.
Qed.

Lemma value_uincl_wf_results m1 m2 fn vargs1 vargs2 vargs1' vargs2' m vres1 vres2 :
  wf_args m1 m2 fn vargs1 vargs2 ->
  List.Forall2 value_uincl vargs1' vargs1 ->
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2' ->
  List.Forall (fun oi => forall i, oi = Some i -> nth None (local_alloc fn).(sao_params) i <> None) (local_alloc fn).(sao_return) ->
  wf_results m vargs1' vargs2' fn vres1 vres2 ->
  wf_results m vargs1 vargs2 fn vres1 vres2.
Proof.
  move=> hargs hincl hptreq hnnone.
  apply Forall3_impl_in.
  move=> [i|//] vr1 vr2 hoi _ _ [p [-> hresultp]].
  exists p; split; first by reflexivity.
  have /List.Forall_forall -/(_ _ hoi _ refl_equal) := hnnone.
  case hpi: nth => [pi|//] _.
  case: (hresultp) => hrargs hsub hread.
  split=> //.
  + by rewrite (Forall3_nth hptreq None (Vbool true) (Vbool true)
      (nth_not_default hpi ltac:(discriminate)) ltac:(congruence)).
  have := Forall2_nth hincl (Vbool true) (Vbool true).
  have -> := Forall2_size hincl.
  have [<- _] := Forall3_size hargs.
  move=> /(_ _ (nth_not_default hpi ltac:(discriminate))).
  move=> /value_uincl_subtype.
  by apply subtype_trans.
Qed.

Lemma free_stack_spec_wf_results m1 m2 fn vargs1 vargs2 m3 m3' vres1 vres2 :
  wf_args m1 m3 fn vargs1 vargs2 ->
  validw m3 =2 validw m3' ->
  free_stack_spec m2 m3' ->
  List.Forall (fun oi => forall i, oi = Some i -> nth None (local_alloc fn).(sao_params) i <> None) (local_alloc fn).(sao_return) ->
  wf_results m2 vargs1 vargs2 fn vres1 vres2 ->
  wf_results m3' vargs1 vargs2 fn vres1 vres2.
Proof.
  move=> hargs hvalid hfss hforall.
  apply Forall3_impl_in.
  move=> [i|//] vr1 vr2 hoi _ _ [p [-> hresultp]].
  exists p; split; first by reflexivity.
  have /List.Forall_forall -/(_ _ hoi _ refl_equal) := hforall.
  case hpi: nth => [pi|//] _.
  case: (hresultp) => hrargs hsub hread.
  split=> //.
  move=> off w /dup[] /get_val_byte_bound hoff.
  rewrite -hfss.(fss_read_old8); first by apply hread.
  have := Forall3_nth hargs None (Vbool true) (Vbool true) (nth_not_default hpi ltac:(discriminate)).
  rewrite hpi /= hrargs.
  move=> [_ [[<-] hargp]].
  rewrite -hvalid.
  apply hargp.(wap_valid).
  apply: between_byte hoff.
  + by apply (no_overflow_incl (zbetween_le _ (size_of_le hsub)) hargp.(wap_no_overflow)).
  by apply: zbetween_le (size_of_le hsub).
Qed.

Lemma List_Forall3_inv A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  Forall3 R l1 l2 l3 ->
  match l1 with
  | [::] =>
    match l2, l3 with
    | [::], [::] => True
    | _, _ => False
    end
  | a :: l1 =>
    match l2, l3 with
    | b :: l2, c :: l3 => R a b c /\ Forall3 R l1 l2 l3
    | _, _ => False
    end
  end.
Proof. by case. Qed.

(* TODO: choose a better name *)
Lemma value_uincl_disjoint_from_writable_params fn vargs1 vargs1' vargs2 vargs2' p :
  List.Forall2 value_uincl vargs1' vargs1 ->
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2' ->
  disjoint_from_writable_params fn p vargs1 vargs2 ->
  disjoint_from_writable_params fn p vargs1' vargs2'.
Proof.
  rewrite /disjoint_from_writable_params.
  move=> hincl hptreq hdisj.
  elim: {vargs1 vargs2} hdisj vargs1' hincl vargs2' hptreq.
  + move=> _ /List_Forall2_inv_r -> vargs2 hdisj.
    inversion_clear hdisj.
    by constructor.
  move=> opi varg1 varg2 sao_params vargs1 vargs2 hdisj _ ih.
  move=> _ /List_Forall2_inv_r [varg1' [vargs1' [-> [hincl /ih{ih}ih]]]].
  move=> [|varg2' vargs2'] /List_Forall3_inv // [hptreq /ih{ih}ih].
  constructor=> //.
  move=> pi p2 ?? hw; subst opi varg2'.
  apply (disjoint_zrange_incl_l (zbetween_le _ (size_of_le (value_uincl_subtype hincl)))).
  rewrite /disjoint_from_writable_param in hdisj.
  by apply (hdisj _ _ refl_equal (hptreq ltac:(discriminate)) hw).
Qed.

(* sem_call has 7 steps that are reflected in this proof:
  - truncate_val of args,
  - init_state,
  - write_vars of args,
  - execution of the body,
  - get_var of results,
  - truncate_val of results,
  - finalize.
*)
Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
Proof.
  move=> m1 _ fn fd vargs1' vargs1 _ s1 s1' vres1 vres1' hfd hvargs1' /= [<-] hs1 hsem1 Hc hvres1 hvres1' ->.
  move=> m2 vargs2 hext hargs hdisjv hok.
  have [fd2 [] hfd2] := Halloc_fd hfd.
  rewrite /alloc_fd /=.
  t_xrbindP=> fd2' stack hlayout [[locals1 rmap1] vnew1] hlocal_map.
  t_xrbindP=> -[[[vnew2 locals2] rmap2] alloc_params].
  apply: add_err_funP => hparams.
  t_xrbindP=> _ /assertP /ZleP hextra _ /assertP /ZleP hmax.
  move=> [rmap3 c].
  apply: add_finfoP => halloc.
  t_xrbindP=> res.
  apply: add_err_funP => hcresults ??; subst fd2 fd2'.

  (* truncate_val of args *)
  have [vargs2' [hvargs2' hargs']] := mapM2_truncate_val_wf_args hargs hvargs1'.
  have huincl := mapM2_truncate_val_value_uincl hvargs1'.
  have hptreq := mapM2_truncate_val_ptr_eq hargs hvargs2'.
  have hdisjv' := value_uincl_disjoint_values hargs hdisjv huincl hptreq.

  (* init_state *)
  have [m2' halloc_stk]: exists m2',
    alloc_stack m2 (sao_align (local_alloc fn)) (sao_size (local_alloc fn)) (sao_extra_size (local_alloc fn)) = ok m2'.
  + apply Memory.alloc_stack_complete.
    apply /and3P; split.
    + apply /ZleP.
      by apply (init_stack_layout_size_ge0 hlayout).
    + by apply /ZleP.
    move: hok; rewrite /alloc_ok => /(_ _ hfd2) /=; rewrite /allocatable_stack => -[hallocatable hal].
    case: is_RAnone hal hmax => [_|-> //] hmax; last by apply /ZleP; lia.
    case: is_align; last by apply /ZleP; lia.
    apply /ZleP.
    have := round_ws_range (sao_align (local_alloc fn)) (sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)).
    by lia.
  have hass := Memory.alloc_stackP halloc_stk.
  set fex := {| sf_align := _ |} in hfd2.
  set rsp := top_stack m2'.
  have hinit: init_stk_state fex (p_extra P') rip {| emem := m2; evm := vmap0 |} =
    ok {| emem := m2';
          evm  := vmap0.[x86_variables.var_of_register RSP <- ok (pword_of_word rsp)]
                       .[{|vtype := sword64; vname := P'.(p_extra).(sp_rip)|} <- ok (pword_of_word rip)] |}.
  + by rewrite /init_stk_state halloc_stk /= !pword_of_wordE.
  have hover := ass_no_overflow hass.
  have hargs'' := alloc_stack_spec_wf_args hargs' hass.
  have hext' := alloc_stack_spec_extend_mem hext hass.

  have hdisj_glob_locals: 0 < glob_size -> 0 < (local_alloc fn).(sao_size) ->
    disjoint_zrange rip glob_size rsp (sao_size (local_alloc fn)).
  + move=> hlt1 hlt2.
    apply disjoint_zrange_sym.
    apply disjoint_zrange_U8 => //.
    move=> k hk.
    have hb: between rip glob_size (rip + wrepr _ k)%R U8.
    + apply: between_byte hk => //.
      by apply zbetween_refl.
    (* TODO: use disjoint_zrange in ass_fresh? *)
    have /hass.(ass_fresh) hfresh: validw m2 (rip + wrepr _ k)%R U8.
    + apply hext.(em_valid).
      by rewrite hb orbT.
    apply disjoint_zrange_sym.
    split=> //.
    by apply: (no_overflow_incl hb).
  have hdisj_locals_params:
    Forall3 (fun opi varg1 varg2 => forall pi, opi = Some pi ->
      forall (p:ptr), varg2 = Vword p -> 0 < (local_alloc fn).(sao_size) -> disjoint_zrange rsp (local_alloc fn).(sao_size) p (size_val varg1))
    (sao_params (local_alloc fn)) vargs1' vargs2'.
  + apply: Forall3_impl hargs'.
    move=> opi varg1 varg2 harg pi ? p ? hlt; subst opi varg2.
    case: harg => _ [[<-] hargp].
    apply disjoint_zrange_U8 => //.
    + by apply size_of_gt0.
    + by apply hargp.(wap_no_overflow).
    move=> k hk.
    have hb: between p (size_val varg1) (p + wrepr _ k) U8.
    + apply: between_byte hk.
      + by apply hargp.(wap_no_overflow).
      by apply zbetween_refl.
    have hfresh := hass.(ass_fresh) (hargp.(wap_valid) hb).
    apply disjoint_zrange_sym.
    split=> //.
    by apply: no_overflow_incl hb hargp.(wap_no_overflow).

  have hsub := write_vars_subtype (init_params_sarr hparams) hs1. (* 'backported' from write_vars of args *)
  (* TODO:
     - extend_mem implies no_overflow, duplicate! -> maybe we can move no_overflow hyp in LOCAL section
     - disjoint_zrange rsp rip implies no_overflow rip et no_overflow rsp, duplicates!
  *)
  have /= hvs := init_stk_state_valid_state hlayout hover hdisj_glob_locals
    hargs' hsub hlocal_map hparams hext hass refl_equal rip_rsp_neq.
  have hpmap := init_params_wf_pmap hlayout rsp vargs1' vargs2' hlocal_map hparams.
  (* TODO: [vrip] appears only because we need a default value in [get_pi_nth].
     It does not seem very clean to me.
  *)
  have hslots := Hwf_Slots hlayout hover hdisj_glob_locals hext.(em_align)
    hass.(ass_align_stk) hargs' hdisjv' hsub (p_extra P').(sp_rip) hparams hdisj_locals_params.

  (* write_vars of args *)
  have [s2 [hs2 hvs']] := valid_state_init_params hlayout hargs'' hlocal_map hparams hvs hs1.
  have hext'': extend_mem (emem s1) (emem s2) rip global_data.
  + have /= <- := write_vars_emem hs1.
    by have /= <- := write_vars_emem hs2.

  have hsao: wf_sao rsp (emem s2) (local_alloc fn).
  + have /= <- := write_vars_emem hs2.
    split.
    + rewrite /enough_size /allocatable_stack.
      split; first by lia.
      rewrite /top_stack hass.(ass_frames) /= hass.(ass_limit).
      move: hok; rewrite /alloc_ok => /(_ _ hfd2) /= []; rewrite /allocatable_stack.
      have hsize := init_stack_layout_size_ge0 hlayout.
      assert (hge := ge0_wunsigned (stack_limit m2)).
      have hpos := wsize_size_pos (sao_align (local_alloc fn)).
      case: is_RAnone hmax.
      + move=> hmax hok _.
        have hbound: 0 <= sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)
                  /\ sao_size (local_alloc fn) + sao_extra_size (local_alloc fn) <= wunsigned (top_stack m2).
        + by lia.
        have := @top_stack_after_alloc_bounded _ (local_alloc fn).(sao_align) _ hbound.
        by lia.
      move=> hmax hok1 hok2.
      rewrite (top_stack_after_aligned_alloc _ (hok2 _)) //.
      rewrite wunsigned_add; first by lia.
      split; first by lia.
      assert (hrange := wunsigned_range (top_stack m2)).
      have [? _] := round_ws_range (sao_align (local_alloc fn)) (sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)).
      by lia.
   by apply hass.(ass_align_stk).

  (* execution of the body *)
  (* TODO: hext''' can be deduced from valid_state_extend_mem, is it really needed ? *)
  have [s2' [hsem2 hvs''']] := Hc _ _ _ _ _ _ _ _ _ hpmap hslots _ halloc _ _ hvs' hext'' hsao.
  have hext''' := valid_state_extend_mem hslots hvs' hext'' hvs''' (sem_validw_stable_uprog hsem1) (sem_validw_stable_sprog hsem2).

  (* get_var of results *)
  have harr: List.Forall2 (fun osr (x : var_i) => osr <> None -> is_sarr (vtype x)) (map fst alloc_params) (f_params fd).
  + by apply: (Forall2_trans _ (init_params_alloc_params_not_None hparams) (init_params_sarr hparams)); auto.
  have hsub' := write_vars_subtype harr hs1.
  have haddr := init_params_alloc_params rsp hargs'' hparams.
  have [vres2 [hvres2 hresults]] := check_resultsP hvs''' hsub' haddr hcresults hvres1.

  (* truncate_val of results *)
  have [vres2' [hvres2' hresults']] := mapM2_truncate_val_wf_results hresults hvres1'.
  have hnnone: List.Forall (fun oi => forall i, oi = Some i -> nth None (sao_params (local_alloc fn)) i <> None)
                           (sao_return (local_alloc fn)).
  + apply: List.Forall_impl (check_results_alloc_params_not_None hcresults).
    move=> oi hnnone i ?; subst oi.
    move: hnnone => /(_ _ refl_equal).
    case hsr: nth => [sr|//] _.
    apply (Forall2_nth (init_params_alloc_params_not_None hparams) None None (nth_not_default hsr ltac:(discriminate))).
    by rewrite hsr.
  have hresults'' := value_uincl_wf_results hargs huincl hptreq hnnone hresults'.

  (* finalize *)
  have hfss := Memory.free_stackP (emem s2').
  have hvalideq1: validw m1 =2 validw (emem s1').
  + have /= -> := write_vars_emem hs1.
    by apply (sem_validw_stable_uprog hsem1).
  have hvalideq2: validw m2 =2 validw (free_stack (emem s2')).
  + apply: (alloc_free_validw_stable hass _ _ hfss);
      have /= -> := write_vars_emem hs2.
    + by apply (sem_stack_stable_sprog hsem2).
    by apply (sem_validw_stable_sprog hsem2).
  have hresults''' := free_stack_spec_wf_results hargs hvalideq2 hfss hnnone hresults''.

  exists (free_stack (emem s2')), vres2'.
  split.
  + by econstructor; try eassumption.
  split.
  + apply (free_stack_spec_extend_mem hext''' hfss).
    move=> p.
    rewrite -hvalideq1 -hvalideq2.
    by apply hext.(em_valid).
  split=> //.
  rewrite /mem_unchanged_params.
  move=> p hvalid1 hvalid2 hdisjp.
  rewrite -hfss.(fss_read_old8) -?hvalideq2 //.
  have /vs_unchanged := hvs'''; apply => //.
  + by rewrite -hvalideq1.
  apply (disjoint_from_writable_params_all_slots hlayout hover hdisj_glob_locals hargs'' hsub P'.(p_extra).(sp_rip) hparams).
  + by apply (value_uincl_disjoint_from_writable_params huincl hptreq hdisjp).
  have ? := hass.(ass_fresh) hvalid1.
  split.
  + by apply hover.
  + apply is_align_no_overflow.
    by apply is_align8.
  by apply or_comm.
Qed.

Lemma check_cP m1 fn vargs m2 vres : sem_call P ev m1 fn vargs m2 vres -> Pfun m1 fn vargs m2 vres.
Proof.
  apply (@sem_call_Ind _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
                       Hskip
                       Hcons
                       HmkI
                       Hassgn
                       Hopn
                       Hif_true
                       Hif_false
                       Hwhile_true
                       Hwhile_false
                       Hfor
                       Hfor_nil
                       Hfor_cons
                       Hcall
                       Hproc).
Qed.

End PROC.

End INIT.

(* TODO: could be generalized to speak only about mapM and assoc *)
Lemma mapM_alloc_fd_get_fundef p_extra mglob oracle fds1 fds2 :
  mapM (alloc_fd p_extra mglob oracle) fds1 = ok fds2 ->
  forall fn fd1,
  get_fundef fds1 fn = Some fd1 ->
  exists fd2, get_fundef fds2 fn = Some fd2 /\
              alloc_fd p_extra mglob oracle (fn, fd1) = ok (fn, fd2).
Proof.
  move=> halloc fn fd1.
  elim: fds1 fds2 halloc => //=.
  move=> [fn' fd1'] fds1 ih.
  t_xrbindP=> _ [fn'' fd2'] halloc fds2 /ih{ih}ih <- /=.
  have ?: fn'' = fn'; last subst fn''.
  + by move: halloc; rewrite /alloc_fd; t_xrbindP.
  case: eqP => //=.
  by move=> -> [<-]; exists fd2'.
Qed.

(* Here are informal descriptions of the predicates used in the theorem.

   - extend_mem m1 m2 rip data: [m2] is a memory that contains at least [m1]
       and (disjointly) data [data] at adress [rip];

   - wf_args: link between the values taken as arguments in the source and the target
       (complex predicate if the argument is a reg ptr, just equality otherwise);

   - disjoint_values: the writable [reg ptr]s taken as arguments point to disjoint
       zones in memory;

   - alloc_ok: the call is possible in the target (there is enough space in the
       stack, and the top of the stack is aligned if the callee is not an export function);

   - wf_results: link between the values returned in the source and the target
       (complex predicate if the result is a reg ptr, just equality otherwise);

   - mem_unchanged_params: the function call does not modify the stack region,
      except for the regions pointed to by the writable [reg ptr]s given as arguments.
*)
Theorem alloc_progP nrip data oracle_g oracle (P: uprog) (SP: sprog) fn:
  alloc_prog nrip data oracle_g oracle P = ok SP ->
  forall ev m1 vargs1 m1' vres1,
    sem_call (sCP := sCP_unit) P ev m1 fn vargs1 m1' vres1 ->
    forall rip m2 vargs2,
      extend_mem m1 m2 rip data ->
      wf_args data rip oracle m1 m2 fn vargs1 vargs2 ->
      disjoint_values (oracle fn).(sao_params) vargs1 vargs2 ->
      alloc_ok SP fn m2 ->
      exists m2' vres2,
        sem_call (sCP := sCP_stack) SP rip m2 fn vargs2 m2' vres2 /\
        extend_mem m1' m2' rip data /\
        wf_results oracle m2' vargs1 vargs2 fn vres1 vres2 /\
        mem_unchanged_params oracle fn m1 m2 m2' vargs1 vargs2.
Proof.
  move=> hprog ev m1 vargs1 m1' vres1 hsem1 rip m2 vargs2 hext hargs hdisj halloc.
  move: hprog; rewrite /alloc_prog.
  t_xrbindP=> mglob.
  apply: add_err_msgP => hmap.
  case: eqP => [//|hneq].
  case: ifP => [hcheck|//].
  t_xrbindP=> fds hfds.
  set P' := {| p_funcs := _ |} => ?; subst SP.

  have [fd1 hfd1]: exists fd, get_fundef (p_funcs P) fn = Some fd.
  + have /sem_callE [fd1 [hfd1 _]]  := hsem1.
    by exists fd1.

  by apply (check_cP hext.(em_no_overflow) hmap hcheck (P':=P') refl_equal (mapM_alloc_fd_get_fundef hfds)
              hneq hsem1 hext hargs hdisj halloc).
Qed.
