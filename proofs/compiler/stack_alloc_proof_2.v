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

Lemma alloc_free_stack_stable m1 ws sz sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  stack_stable m2 m2' ->
  free_stack_spec m2' m3 ->
  stack_stable m1 m3.
Proof.
  move=> hass hss hfss.
  split.
  + by rewrite hfss.(fss_root) -hss.(ss_root) hass.(ass_root).
  + by rewrite hfss.(fss_limit) -hss.(ss_limit) hass.(ass_limit).
  by rewrite hfss.(fss_frames) -hss.(ss_frames) hass.(ass_frames).
Qed.

Lemma alloc_free_validw_stable m1 ws sz sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  stack_stable m2 m2' ->
  validw m2 =2 validw m2' ->
  free_stack_spec m2' m3 ->
  validw m1 =2 validw m3.
Proof.
  move=> hass hss hvalid hfss.
  move=> p ws'.
  congr (_ && _).
  apply: all_ziota => i hi.
  rewrite !valid8_validw.
  rewrite hfss.(fss_valid) -hvalid hass.(ass_valid).
  rewrite -hss.(ss_top_stack) -(alloc_free_stack_stable hass hss hfss).(ss_top_stack).
  rewrite /pointer_range.
  have [L H] := ass_above_limit hass.
  case: (@andP (_ <=? _)%Z); rewrite !zify.
  - case => ptr_i_lo ptr_i_hi.
    rewrite andbF; apply/negbTE; apply: stack_region_is_free.
    split; last exact: ptr_i_hi.
    etransitivity; last exact: ptr_i_lo.
    exact: L.
  rewrite andbT => ptr_not_fresh.
  set X := (X in _ || X).
  suff /negbTE -> : ~~ X; first by rewrite orbF.
  subst X; rewrite !zify => - [].
  change (wsize_size U8) with 1%Z.
  move => ptr_i_lo ptr_i_hi.
  apply: ptr_not_fresh.
  split; first exact: ptr_i_lo.
  move: H ptr_i_hi; clear => n.
  lia.
Qed.

(* TODO: move (psem_facts ?) *)
(* sem_stack_stable and sem_validw_stable both for uprog and sprog *)
(* TODO: see if we can share some proofs between this and what is in sem_one_varmap_facts *)
Section VALIDW_STABLE. (* taken from sem_one_varmap_facts *)

Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =2 validw m2.
Infix "≡" := mem_equiv (at level 40).

Hypothesis finalize_cancel_init : forall s1 s2 m2 ef,
  init_state ef P.(p_extra) ev s1 = ok s2 ->
  emem s2 ≡ m2 ->
  emem s1 ≡ finalize ef m2.

Instance mem_equiv_trans : Transitive mem_equiv.
Proof.
  move => m1 m2 m3 [hss1 hvalid1] [hss2 hvalid2].
  split; first by transitivity m2.
  by move=> p ws; transitivity (validw m2 p ws).
Qed.

Lemma write_lval_validw gd x v s s' :
  write_lval gd x v s = ok s' ->
  validw (emem s) =2 validw (emem s').
Proof.
  case: x => /=.
  - by move => _ ty /write_noneP [] <-.
  - by move => x /write_var_emem <-.
  - t_xrbindP => /= ????? ?? ?? ? ? ? ? ? h <- /=.
    by move=> ??; rewrite (write_validw_eq h).
  - move => aa sz x e.
    by apply: on_arr_varP; t_xrbindP => ?????????????? <-.
  move => aa sz ty x e.
  by apply: on_arr_varP; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_validw gd xs vs s s' :
  write_lvals gd s xs vs = ok s' ->
  validw (emem s) =2 validw (emem s').
Proof.
  elim: xs vs s.
  - by case => // ? [] ->.
  move => x xs ih [] // v vs s /=; t_xrbindP => ? /write_lval_validw h /ih.
  by move=> h1 p ws; rewrite h h1.
Qed.

Let Pc s1 (_: cmd) s2 : Prop := emem s1 ≡ emem s2.
Let Pi s1 (_: instr) s2 : Prop := emem s1 ≡ emem s2.
Let Pi_r s1 (_: instr_r) s2 : Prop := emem s1 ≡ emem s2.
Let Pfor (_: var_i) (_: seq Z) s1 (_: cmd) s2 : Prop := emem s1 ≡ emem s2.
Let Pfun m1 (_: funname) (_: seq value) m2 (_: seq value) : Prop := m1 ≡ m2.

Lemma mem_equiv_nil : sem_Ind_nil Pc.
Proof. by []. Qed.

Lemma mem_equiv_cons : sem_Ind_cons P ev Pc Pi.
Proof. by move => x y z i c _ xy _ yz; red; etransitivity; eassumption. Qed.

Lemma mem_equiv_mkI : sem_Ind_mkI P ev Pi_r Pi.
Proof. by []. Qed.

Lemma mem_equiv_assgn : sem_Ind_assgn P Pi_r.
Proof. by move => s1 s2 x tg ty e v v' ok_v ok_v' /dup[] /write_lval_validw ? /write_lval_stack_stable. Qed.

Lemma mem_equiv_opn : sem_Ind_opn P Pi_r.
Proof. by move => s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => ???? /dup[] /write_lvals_validw ? /write_lvals_stack_stable. Qed.

Lemma mem_equiv_if_true : sem_Ind_if_true P ev Pc Pi_r.
Proof. by []. Qed.

Lemma mem_equiv_if_false : sem_Ind_if_false P ev Pc Pi_r.
Proof. by []. Qed.

Lemma mem_equiv_while_true : sem_Ind_while_true P ev Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 aa c e c' _ A _ _ B _ C; red.
  etransitivity; first exact: A.
  etransitivity; first exact: B.
  exact: C.
Qed.

Lemma mem_equiv_while_false : sem_Ind_while_false P ev Pc Pi_r.
Proof. by []. Qed.

Lemma mem_equiv_for : sem_Ind_for P ev Pi_r Pfor.
Proof. by []. Qed.

Lemma mem_equiv_for_nil : sem_Ind_for_nil Pfor.
Proof. by []. Qed.

Lemma mem_equiv_for_cons : sem_Ind_for_cons P ev Pc Pfor.
Proof.
  move => ???????? /write_var_emem A _ B _ C; red.
  rewrite A; etransitivity; [ exact: B | exact: C ].
Qed.

Lemma mem_equiv_call : sem_Ind_call P ev Pi_r Pfun.
Proof. move=> s1 m2 s2 ii xs fn args vargs vres _ _ ? /dup[] /write_lvals_validw ? /write_lvals_stack_stable ?; red; etransitivity; [|split]; eassumption. Qed.

Lemma mem_equiv_proc : sem_Ind_proc P ev Pc Pfun.
Proof.
  move=> m1 m2 fn fd vargs vargs' s0 s1 s2 vres vres' ok_fd ok_vargs ok_s0 ok_s1 _ Hc _ _ ->.
  rewrite /Pc -(write_vars_emem ok_s1) in Hc.
  by apply (finalize_cancel_init ok_s0 Hc).
Qed.

Lemma sem_mem_equiv s1 c s2 :
  sem P ev s1 c s2 → emem s1 ≡ emem s2.
Proof.
  by apply
    (@sem_Ind _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
              mem_equiv_nil
              mem_equiv_cons
              mem_equiv_mkI
              mem_equiv_assgn
              mem_equiv_opn
              mem_equiv_if_true
              mem_equiv_if_false
              mem_equiv_while_true
              mem_equiv_while_false
              mem_equiv_for
              mem_equiv_for_nil
              mem_equiv_for_cons
              mem_equiv_call
              mem_equiv_proc).
Qed.

Lemma sem_I_mem_equiv s1 i s2 :
  sem_I P ev s1 i s2 → emem s1 ≡ emem s2.
Proof.
  by apply
    (@sem_I_Ind _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
                mem_equiv_nil
                mem_equiv_cons
                mem_equiv_mkI
                mem_equiv_assgn
                mem_equiv_opn
                mem_equiv_if_true
                mem_equiv_if_false
                mem_equiv_while_true
                mem_equiv_while_false
                mem_equiv_for
                mem_equiv_for_nil
                mem_equiv_for_cons
                mem_equiv_call
                mem_equiv_proc).
Qed.

Lemma sem_i_mem_equiv s1 i s2 :
  sem_i P ev s1 i s2 → emem s1 ≡ emem s2.
Proof.
  by apply
    (@sem_i_Ind _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
                mem_equiv_nil
                mem_equiv_cons
                mem_equiv_mkI
                mem_equiv_assgn
                mem_equiv_opn
                mem_equiv_if_true
                mem_equiv_if_false
                mem_equiv_while_true
                mem_equiv_while_false
                mem_equiv_for
                mem_equiv_for_nil
                mem_equiv_for_cons
                mem_equiv_call
                mem_equiv_proc).
Qed.

Lemma sem_call_mem_equiv m1 fn vargs m2 vres :
  sem_call P ev m1 fn vargs m2 vres → m1 ≡ m2.
Proof.
  by apply
    (@sem_call_Ind _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
                   mem_equiv_nil
                   mem_equiv_cons
                   mem_equiv_mkI
                   mem_equiv_assgn
                   mem_equiv_opn
                   mem_equiv_if_true
                   mem_equiv_if_false
                   mem_equiv_while_true
                   mem_equiv_while_false
                   mem_equiv_for
                   mem_equiv_for_nil
                   mem_equiv_for_cons
                   mem_equiv_call
                   mem_equiv_proc).
Qed.

End VALIDW_STABLE.

Lemma sem_stack_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem p ev s1 c s2 -> stack_stable (emem s1) (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_validw_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem p ev s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_i_validw_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem_i p ev s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_i_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_I_validw_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem_I p ev s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_I_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_call_validw_stable_uprog (p : uprog) (ev : unit) m1 fn vargs m2 vres :
  sem_call p ev m1 fn vargs m2 vres ->
  validw m1 =2 validw m2.
Proof.
  apply sem_call_mem_equiv => {m1 fn vargs m2 vres}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

(* Already proved in psem_facts as [sem_stack_stable] *)
Lemma sem_stack_stable_sprog (p : sprog) (gd : ptr) s1 c s2 :
  sem p gd s1 c s2 -> stack_stable (emem s1) (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_call_stack_stable_sprog (p : sprog) (gd : ptr) m1 fn vargs m2 vres :
  sem_call p gd m1 fn vargs m2 vres -> stack_stable m1 m2.
Proof.
  apply sem_call_mem_equiv => {m1 fn vargs m2 vres}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_validw_stable_sprog (p : sprog) (gd : ptr) s1 c s2 :
  sem p gd s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_i_validw_stable_sprog (p : sprog) (gd : ptr) s1 c s2 :
  sem_i p gd s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_i_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_I_validw_stable_sprog (p : sprog) (gd : ptr) s1 c s2 :
  sem_I p gd s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_I_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_call_validw_stable_sprog (p : sprog) (gd : ptr) m1 fn vargs m2 vres :
  sem_call p gd m1 fn vargs m2 vres ->
  validw m1 =2 validw m2.
Proof.
  apply sem_call_mem_equiv => {m1 fn vargs m2 vres}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

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
Hypothesis Hsize_le : Forall3 (fun opi (x:var_i) v => opi <> None -> size_slot x <= size_val v) sao.(sao_params) params vargs1.
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

Definition add_alloc fn stack globals' (xpk:var * ptr_kind_init) (lrx: Mvar.t ptr_kind * region_map * Sv.t) :=
  let '(locals, rmap, sv) := lrx in
  let '(x, pk) := xpk in
  if Sv.mem x sv then stack_alloc.cferror fn "invalid reg pointer, please report"%string
  else if Mvar.get locals x is Some _ then
    stack_alloc.cferror fn "the oracle returned two results for the same var, please report"%string
  else
    Let svrmap := 
      match pk with
      | PIdirect x' z sc =>
        let vars := if sc is Slocal then stack else globals' in
        match Mvar.get vars x' with
        | None => stack_alloc.cferror fn "unknown region, please report"%string
        | Some (ofs', ws') =>
          if [&& (size_slot x <= z.(z_len))%CMP, (0%Z <= z.(z_ofs))%CMP &
                 ((z.(z_ofs) + z.(z_len))%Z <= size_slot x')%CMP] then
            let rmap :=
              if sc is Slocal then
                let sr := sub_region_stack x' ws' z in
                Region.set_arr_init rmap x sr
              else
                rmap
            in
            ok (sv, Pdirect x' ofs' ws' z sc, rmap)
          else stack_alloc.cferror fn "invalid slot, please report"%string
        end
      | PIstkptr x' z xp =>
        if ~~ is_sarr x.(vtype) then
          stack_alloc.cferror fn "a stk ptr variable should be an array, please report"%string
        else
        match Mvar.get stack x' with
        | None => stack_alloc.cferror fn "unknown stack region, please report"%string
        | Some (ofs', ws') =>
          if Sv.mem xp sv then stack_alloc.cferror fn "invalid stk ptr (not uniq), please report"%string
          else if xp == x then stack_alloc.cferror fn "a pseudo-var is equal to a program var, please report"%string
          else if Mvar.get locals xp is Some _ then stack_alloc.cferror fn "a pseudo-var is equal to a program var, please report"%string
          else
            if [&& (Uptr <= ws')%CMP,
                (0%Z <= z.(z_ofs))%CMP,
                (Z.land z.(z_ofs) (wsize_size U64 - 1) == 0)%Z,
                (wsize_size Uptr <= z.(z_len))%CMP &
                ((z.(z_ofs) + z.(z_len))%Z <= size_slot x')%CMP] then
              ok (Sv.add xp sv, Pstkptr x' ofs' ws' z xp, rmap)
          else stack_alloc.cferror fn "invalid ptr kind, please report"%string
        end
      | PIregptr p => 
        if ~~ is_sarr x.(vtype) then
          stack_alloc.cferror fn "a reg ptr variable should be an array, please report"%string
        else
        if Sv.mem p sv then stack_alloc.cferror fn "invalid reg pointer already exists, please report"%string
        else if Mvar.get locals p is Some _ then stack_alloc.cferror fn "a pointer is equal to a program var, please report"%string
        else if vtype p != sword Uptr then stack_alloc.cferror fn "invalid pointer type, please report"%string
        else ok (Sv.add p sv, Pregptr p, rmap) 
      end in
    let '(sv,pk, rmap) := svrmap in
    let locals := Mvar.set locals x pk in
    ok (locals, rmap, sv).

Lemma init_local_map_eq :
  init_local_map vrip0 vrsp0 fn mglob stack sao =
    let sv := Sv.add vrip0 (Sv.add vrsp0 Sv.empty) in
    Let aux := foldM (add_alloc fn stack mglob) (Mvar.empty _, Region.empty, sv) sao.(sao_alloc) in
    let '(locals, rmap, sv) := aux in
    ok (locals, rmap, sv).
Proof. done. Qed.

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

(* TODO: move? *)
Lemma Forall2_impl A B (R1 R2 : A -> B -> Prop) :
  (forall a b, R1 a b -> R2 a b) ->
  forall l1 l2,
  List.Forall2 R1 l1 l2 ->
  List.Forall2 R2 l1 l2.
Proof.
  move=> himpl l1 l2 hforall.
  elim: hforall; eauto.
Qed.
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

Lemma Forall3_forall A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  Forall3 R l1 l2 l3 ->
  forall a b c, List.In (a, (b, c)) (zip l1 (zip l2 l3)) -> R a b c.
Proof.
  elim {l1 l2 l3} => // a b c l1 l2 l3 h hforall ih a2 b2 c2 /=.
  case.
  + by move=> [<- <- <-].
  by apply ih.
Qed.

Lemma forall_Forall3 A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  size l1 = size l2 -> size l1 = size l3 ->
  (forall a b c, List.In (a, (b, c)) (zip l1 (zip l2 l3)) -> R a b c) ->
  Forall3 R l1 l2 l3.
Proof.
  elim: l1 l2 l3.
  + by move=> [|//] [|//]; constructor.
  move=> a l1 ih [//|b l2] [//|c l3] [hsize1] [hsize2] hin.
  constructor.
  + by apply hin; left.
  apply ih => //.
  move=> ??? h.
  by apply hin; right.
Qed.

Lemma nth_Forall3 A B C (R : A -> B -> C -> Prop) l1 l2 l3 a b c:
  size l1 = size l2 -> size l1 = size l3 ->
  (forall i, (i < size l1)%nat -> R (nth a l1 i) (nth b l2 i) (nth c l3 i)) ->
  Forall3 R l1 l2 l3.
Proof.
  elim: l1 l2 l3.
  + by move=> [|//] [|//]; constructor.
  move=> a0 l1 ih [//|b0 l2] [//|c0 l3] [hsize1] [hsize2] hnth.
  constructor.
  + by apply (hnth 0%nat).
  apply ih => //.
  move=> i.
  by apply (hnth i.+1).
Qed.

Lemma Forall2_forall A B (R : A -> B -> Prop) l1 l2 :
  List.Forall2 R l1 l2 ->
  forall a b, List.In (a, b) (zip l1 l2) ->
  R a b.
Proof.
  elim=> // a b la lb h hforall ih a2 b2 /=.
  case.
  + by move=> [<- <-].
  by apply ih.
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
  elim: Hsize_le vargs2; first by move=> [].
  move=> opi x varg1 sao_params params' vargs1' hsub _ ih [//|varg2 vargs2'].
  case: opi hsub => [pi'|] hsub; last by apply ih.
  move=> [[<- _ <- _] //|]; last by apply ih.
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
  add_alloc fn stack mglob (x, pki) (locals1', rmap1', vnew1') = ok (locals2', rmap2', vnew2') ->
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
  add_alloc fn stack mglob (x, pki) (locals1', rmap1', vnew1') = ok (locals2', rmap2', vnew2') ->
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
  move: hlocal_map; rewrite init_local_map_eq /=.
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
  move: hlocal_map; rewrite init_local_map_eq /=.
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
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem hglobv htop.
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
(*   (forall i, 0 <= i < glob_size ->
    read (emem s2) (rip + wrepr U64 i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) -> *)
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
    move=> ?. apply /orP; left.
    apply hext.(em_valid).
    apply /orP; left; done.
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

(* [x] is [var_i] so that we can pass [params] (and not [map v_var params]).
   But it is a bit painful, since in some proofs, we have [var] and not [var_i].
   We use [1%positive] as a dummy [v_info] to forge a [var_i].
*)
Definition disjoint_from_writable_param p opi (x:var_i) v2 :=
  forall pi p2, opi = Some pi -> v2 = @Vword Uptr p2 -> pi.(pp_writable) ->
  disjoint_zrange p2 (size_slot x) p (wsize_size U8).

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
  Forall3 (disjoint_from_writable_param p) sao.(sao_params) params vargs2 ->
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
  have := Forall3_nth hdisj None {| v_var := vrip0; v_info := 1%positive |} (Vbool true) hi.
  move: hi; have [-> _] := size_fmapM2 hparams => hi.
  by rewrite hnth2 hnth4 => /(_ _ _ refl_equal refl_equal hw); rewrite -(nth_map _ vrip0 v_var) // hnth1.
Qed.

(* If p is [disjoint_from_writable_params] and from local variables, it is
   disjoint from all writable params.
*)
Corollary disjoint_from_writable_params_all_slots p :
  Forall3 (disjoint_from_writable_param p) sao.(sao_params) params vargs2 ->
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

Lemma zbetween_not_disjoint_zrange p1 s1 p2 s2 :
  zbetween p1 s1 p2 s2 ->
  0 < s2 ->
  ~ disjoint_zrange p1 s1 p2 s2.
Proof. by rewrite /zbetween !zify => hb hlt [_ _ ?]; lia. Qed.

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
  move=> hwf hvs hext rmap' s1' s2' hvs' hvalid1 hvalid2.
  case:(hext) => hover halign hold hfresh hvalid hnew.
  split=> //=.
  + by apply (vs_eq_mem (valid_state := hvs')).
  + move=> p hvalidp.
    apply hfresh.
    by rewrite hvalid1.
  + move=> p.
    rewrite -hvalid1 -hvalid2. by apply hvalid.
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
  rewrite -(vs_unchanged (valid_state:=hvs')) //; last by rewrite -hvalid1.
  rewrite (vs_unchanged (valid_state:=hvs)) //.
  by apply hnew.
Qed.

Section PROC.

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].

Variable (local_alloc : funname -> stk_alloc_oracle_t).

Notation alloc_fd := (alloc_fd true).
Notation alloc_i  := (alloc_i true).

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

Record wf_sao rsp m sao := {
  wf_sao_size     : enough_size m sao;
  wf_sao_align    : is_align rsp sao.(sao_align);
  wf_sao_max_size : 0 <= sao.(sao_max_size);
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
              valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2' /\
              extend_mem (emem s2) (emem s2') rip global_data.

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
              valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2' /\
              extend_mem (emem s2) (emem s2') rip global_data.

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
              valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2' /\
              extend_mem (emem s2) (emem s2') rip global_data.

Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

(*
Definition allocatable_stack (m : mem) (z : Z) :=
  (z <= wunsigned (top_stack m) - wunsigned (stack_limit m))%Z.
*)
(* TODO: edit allocatable_stack in low_memory *)
Definition alloc_ok (SP:sprog) fn m2 :=
  forall fd, get_fundef (p_funcs SP) fn = Some fd ->
  allocatable_stack m2 fd.(f_extra).(sf_stk_max) /\
  if is_RAnone fd.(f_extra).(sf_return_address) then True
  else is_align (top_stack m2) fd.(f_extra).(sf_align).

(* Addr ??? *)
(* [glob_size] and [rip] were section variables in stack_alloc_proof.v, they
   are section variables in this file too. Can we put everything in the same
   section? Probably not if the file is split.
*)
Definition wf_args m1 m2 fn :=
  Forall3 (wf_arg glob_size rip m1 m2) (local_alloc fn).(sao_params).
Definition wf_results m vargs1 vargs2 fn :=
  Forall3 (wf_result m vargs1 vargs2) (local_alloc fn).(sao_return).

(* TODO: utiliser les types des paramètres plutôt que les arguments dans le source
   pour connaître la taille des zones mémoires ?
*)
Definition disjoint_from_writable_param p opi (x:var_i) v2 :=
  match opi with
  | Some pi =>
  forall p2, v2 = @Vword Uptr p2 ->
  pi.(pp_writable) -> disjoint_zrange p2 (size_slot x) p (wsize_size U8)
  | None => True
  end.
Definition disjoint_from_writable_params fn p :=
  Forall3 (disjoint_from_writable_param p) (local_alloc fn).(sao_params).
(* TODO: clean *)
Definition mem_unchanged_params fn ms m0 m vargs2 :=
  forall fd, get_fundef P.(p_funcs) fn = Some fd ->
  forall p, validw m0 p U8 -> ~ validw ms p U8 -> disjoint_from_writable_params fn p fd.(f_params) vargs2 ->
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
      mem_unchanged_params fn m1 m1' m2' vargs'.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s pmap rsp Slots Addr Writable Align rmap1 rmap2 /= c2 hpmap hwf sao [??] m0 s' hv hext hsao;subst rmap1 c2.
  exists s'; split => //; exact: Eskip.
Qed.

Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c hhi Hi hhc Hc pmap rsp Slots Addr Writable Align rmap1 rmap3 c1 hpmap hwf sao /=.
  t_xrbindP => -[rmap2 i'] hi {rmap3} [rmap3 c'] hc /= <- <- m0 s1' hv hext hsao.
  have [s2' [si [hv2 hext2]]]:= Hi _ _ _ _ _ _ _ _ _ hpmap hwf _ hi _ _ hv hext hsao.
  have hsao2 := stack_stable_wf_sao (sem_I_stack_stable si) hsao.
  have [s3' [sc [hv3 hext3]]]:= Hc _ _ _ _ _ _ _ _ _ hpmap hwf _ hc _ _ hv2 hext2 hsao2.
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
    exists s2'; split=> //; split=> //.
    apply: (valid_state_extend_mem hwf hvs hext hvs').
    + by apply (write_lval_validw hw).
    by apply (sem_i_validw_stable_sprog hs2').
  t_xrbindP => e'; apply: add_iinfoP => /(alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs) he [rmap2' x'].
  apply: add_iinfoP => hax /= ??; subst rmap2' i2.
  have htyv':= truncate_val_has_type htr.
  have [s2' [/= hw' hvs']]:= alloc_lvalP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap hax hvs htyv' hw.
  exists s2';split; first by apply: Eassgn; eauto; rewrite P'_globs; auto.
  split=> //.
  apply: (valid_state_extend_mem hwf hvs hext hvs').
  + by apply (write_lval_validw hw).
  by apply (write_lval_validw hw').
Qed.

Local Lemma Hopn : sem_Ind_opn P Pi_r.
Proof.
  move=> s1 s2 t o xs es.
  rewrite /sem_sopn; t_xrbindP=> vs va hes hop hw pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP=> -[rmap3 i'] es'; apply: add_iinfoP => he [rmap4 x'];
    apply: add_iinfoP => ha /= [<- <-] <- _ <- m0 s1' hvs hext hsao.
  have [s2' [hw' hvalid']] := alloc_lvalsP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap ha hvs (sopn_toutP hop) hw.
  exists s2'; split; first by constructor;
    rewrite /sem_sopn P'_globs (alloc_esP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs he hes) /= hop.
  split=> //.
  apply: (valid_state_extend_mem hwf hvs hext hvalid').
  + by apply (write_lvals_validw hw).
  by apply (write_lvals_validw hw').
Qed.

Lemma incl_var_region rmap1 rmap2 x sr :
  incl rmap1 rmap2 ->
  Mvar.get rmap1.(var_region) x = Some sr ->
  Mvar.get rmap2.(var_region) x = Some sr.
Proof.
  move=> /andP [hincl _] hget1.
  have /Mvar.inclP -/(_ x) := hincl.
  rewrite hget1.
  by case: Mvar.get => // _ /eqP <-.
Qed.

Lemma subset_empty bytes : ByteSet.subset ByteSet.empty bytes.
Proof. by apply /ByteSet.subsetP=> ?; rewrite ByteSet.emptyE. Qed.

Lemma incl_get_var_bytes rmap1 rmap2 r x :
  incl rmap1 rmap2 ->
  ByteSet.subset (get_var_bytes rmap1 r x) (get_var_bytes rmap2 r x).
Proof.
  move=> /andP [] _ /Mr.inclP /(_ r).
  rewrite /get_var_bytes /get_bytes_map /get_bytes.
  case: Mr.get => [bm1|_]; last by apply subset_empty.
  case: Mr.get => [bm2|//].
  move=> /Mvar.inclP /(_ x).
  case: Mvar.get => [bytes1|_]; last by apply subset_empty.
  by case: Mvar.get => [bytes2|//].
Qed.

Lemma subset_refl bytes : ByteSet.subset bytes bytes.
Proof. by apply /ByteSet.subsetP. Qed.

Lemma incl_check_gvalid pmap rmap1 rmap2 x sr bytes :
  incl rmap1 rmap2 ->
  check_gvalid pmap rmap1 x = Some (sr, bytes) ->
  exists bytes2,
  check_gvalid pmap rmap2 x = Some (sr, bytes2) /\ ByteSet.subset bytes bytes2.
Proof.
  move=> hincl.
  rewrite /check_gvalid.
  case: is_glob.
  + move=> ->.
    exists bytes; split=> //.
    by apply subset_refl.
  case heq1: Mvar.get=> [sr'|//] [? <-]; subst sr'.
  rewrite (incl_var_region hincl heq1).
  eexists; split; first by reflexivity.
  apply: incl_get_var_bytes hincl.
Qed.

Lemma subset_bytes_mem bytes1 bytes2 i :
  ByteSet.subset bytes1 bytes2 ->
  ByteSet.mem bytes1 i ->
  ByteSet.mem bytes2 i.
Proof.
  move=> /ByteSet.subsetP hsubset /ByteSet.memP hmem.
  by apply /ByteSet.memP => k /hmem /hsubset.
Qed.

Lemma valid_state_incl pmap rsp Slots Addr Writable Align rmap1 rmap2 m0 s s' :
  incl rmap1 rmap2 ->
  valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap2 m0 s s' ->
  valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap1 m0 s s'.
Proof.
  move=> hincl hvs.
  case:(hvs) => hvalid hdisj hvincl hunch hrip hrsp heqvm hwfr heqmem hglobv htop.
  constructor=> //.
  case: (hwfr) => hwfsr hval hptr; split.
  + move=> x sr /(incl_var_region hincl).
    by apply hwfsr.
  + move=> x sr bytes v /(incl_check_gvalid hincl) [bytes2 [hgvalid2 hsubset]] hget.
    have [hread hty] := hval _ _ _ _ hgvalid2 hget.
    split=> //.
    move=> off hmem.
    apply hread.
    by apply: ByteSet.subsetP hmem.
  move=> x sr /(incl_var_region hincl) /hptr [pk [hlx hpk]].
  exists pk; split=> //.
  case: pk hlx hpk => //= sl ofs ws z f hlx hpk hstkptr.
  apply hpk.
  by apply (subset_bytes_mem (incl_get_var_bytes _ _ hincl)).
Qed.

Lemma subset_inter_l bytes1 bytes2 :
  ByteSet.subset (ByteSet.inter bytes1 bytes2) bytes1.
Proof.
  apply /ByteSet.subsetP => i.
  by rewrite ByteSet.interE => /andP [].
Qed.

Lemma subset_inter_r bytes1 bytes2 :
  ByteSet.subset (ByteSet.inter bytes1 bytes2) bytes2.
Proof.
  apply /ByteSet.subsetP => i.
  by rewrite ByteSet.interE => /andP [].
Qed.

Lemma incl_merge_bytes_l r bm1 bm2 :
  incl_bytes_map r (Mvar.map2 merge_bytes bm1 bm2) bm1.
Proof.
  apply Mvar.inclP => x.
  rewrite Mvar.map2P //.
  rewrite /merge_bytes.
  case: Mvar.get => [bytes1|//].
  case: Mvar.get => [bytes2|//].
  case: ByteSet.is_empty => //.
  by apply subset_inter_l.
Qed.

Lemma incl_merge_bytes_r r bm1 bm2 :
  incl_bytes_map r (Mvar.map2 merge_bytes bm1 bm2) bm2.
Proof.
  apply Mvar.inclP => x.
  rewrite Mvar.map2P //.
  rewrite /merge_bytes.
  case: Mvar.get => [bytes1|//].
  case: Mvar.get => [bytes2|//].
  case: ByteSet.is_empty => //.
  by apply subset_inter_r.
Qed.

Lemma incl_merge_l rmap1 rmap2 : incl (merge rmap1 rmap2) rmap1.
Proof.
  rewrite /merge; apply /andP => /=; split.
  + apply Mvar.inclP => x.
    rewrite Mvar.map2P //.
    case: Mvar.get => [sr1|//].
    case: Mvar.get => [sr2|//].
    by case: ifP.
  apply Mr.inclP => r.
  rewrite Mr.map2P //.
  rewrite /merge_bytes_map.
  case: Mr.get => [bm1|//].
  case: Mr.get => [bm2|//].
  case: Mvar.is_empty => //.
  by apply incl_merge_bytes_l.
Qed.

Lemma incl_merge_r rmap1 rmap2 : incl (merge rmap1 rmap2) rmap2.
Proof.
  rewrite /merge; apply /andP => /=; split.
  + apply Mvar.inclP => x.
    rewrite Mvar.map2P //.
    case: Mvar.get => [sr1|//].
    case: Mvar.get => [sr2|//].
    by case: ifP.
  apply Mr.inclP => r.
  rewrite Mr.map2P //.
  rewrite /merge_bytes_map.
  case: Mr.get => [bm1|//].
  case: Mr.get => [bm2|//].
  case: Mvar.is_empty => //.
  by apply incl_merge_bytes_r.
Qed.

Lemma incl_bytes_map_refl r bm : incl_bytes_map r bm bm.
Proof.
  apply Mvar.inclP => x.
  case: Mvar.get => [bytes|//].
  by apply subset_refl.
Qed.

Lemma incl_refl rmap : incl rmap rmap.
Proof.
  apply /andP; split.
  + apply Mvar.inclP => x.
    case: Mvar.get => [sr|//].
    by apply eq_refl.
  apply Mr.inclP => r.
  case: Mr.get => [bm|//].
  by apply incl_bytes_map_refl.
Qed.

Lemma subset_trans bytes1 bytes2 bytes3 :
  ByteSet.subset bytes1 bytes2 ->
  ByteSet.subset bytes2 bytes3 ->
  ByteSet.subset bytes1 bytes3.
Proof.
  move=> /ByteSet.subsetP h12 /ByteSet.subsetP h23.
  by apply /ByteSet.subsetP; auto.
Qed.

Lemma incl_bytes_map_trans r bm1 bm2 bm3 :
  incl_bytes_map r bm1 bm2 -> incl_bytes_map r bm2 bm3 -> incl_bytes_map r bm1 bm3.
Proof.
  move=> /Mvar.inclP h1 /Mvar.inclP h2.
  apply Mvar.inclP => x.
  case heq1: Mvar.get => [bytes1|//].
  have := h1 x; rewrite heq1.
  case heq2: Mvar.get => [bytes2|//] hsubset.
  have := h2 x; rewrite heq2.
  case heq3: Mvar.get => [bytes3|//].
  by apply (subset_trans hsubset).
Qed.

Lemma incl_trans rmap1 rmap2 rmap3: incl rmap1 rmap2 -> incl rmap2 rmap3 -> incl rmap1 rmap3.
Proof.
  move=> /andP [] /Mvar.inclP h12 /Mr.inclP h12'.
  move=> /andP [] /Mvar.inclP h23 /Mr.inclP h23'.
  apply /andP; split.
  + apply Mvar.inclP => x.
    case heq1: Mvar.get => [sr1|//].
    have := h12 x; rewrite heq1.
    case heq2: Mvar.get => [sr2|//] /eqP ->.
    have := h23 x; rewrite heq2.
    by apply.
  apply Mr.inclP => r.
  case heq1: Mr.get => [bm1|//].
  have := h12' r; rewrite heq1.
  case heq2: Mr.get => [bm2|//] hincl.
  have := h23' r; rewrite heq2.
  case heq3: Mr.get => [bm3|//].
  by apply (incl_bytes_map_trans hincl).
Qed.

Local Lemma Hif_true : sem_Ind_if_true P ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] e'; apply: add_iinfoP => he [rmap4 c1'] hc1 [rmap5 c2'] hc2 /= [??]??? m0 s1' hv hext hsao.
  subst rmap3 i' rmap2 ii1 i2.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv he Hse; rewrite -P'_globs => he'.
  have [s2' [Hsem [Hvalid' Hext']]] := Hc _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ hv hext hsao.
  exists s2'; split; first by apply: Eif_true.
  split=> //.
  by apply: valid_state_incl Hvalid'; apply incl_merge_l.
Qed.

Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] e'; apply: add_iinfoP => he [rmap4 c1'] hc1 [rmap5 c2'] hc2 /= [??]??? m0 s1' hv hext hsao.
  subst rmap3 i' rmap2 ii1 i2.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv he Hse; rewrite -P'_globs => he'.
  have [s2' [Hsem [Hvalid' Hext']]] := Hc _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ _ hv hext hsao.
  exists s2'; split; first by apply: Eif_false.
  split=> //.
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
  have [s2' [hs1 [hv2 hext2]]]:= Hc1 _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ hv hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv2 he Hv; rewrite -P'_globs => he'.
  have hsao2 := stack_stable_wf_sao (sem_stack_stable hs1) hsao.
  have [s3' [hs2 [/(valid_state_incl hincl2) hv3 hext3]]]:= Hc2 _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ _ hv2 hext2 hsao2.
  have /= := Hwhile _ _ _ _ _ _ rmap5 rmap2 ii2 ii2 (Cwhile a c1' e' c2') hpmap hwf sao.
  have hsao3 := stack_stable_wf_sao (sem_stack_stable hs2) hsao2.
  rewrite Loop.nbP /= hc1 /= he /= hc2 /= hincl2 /= => /(_ erefl _ _ hv3 hext3 hsao3) [s4'] [hs3 hv4].
  by exists s4';split => //; apply: Ewhile_true; eassumption.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 a c1 e c2 _ Hc1 Hv pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] [rmap4 [e' [c1' c2']]] /loop2P [rmap5 [rmap6 [hincl1 []]]].
  t_xrbindP => -[rmap7 c11] hc1 /= e1; apply: add_iinfoP => he [rmap8 c22] /= hc2 ????? hincl2 [??]???.
  subst i2 ii1 rmap3 rmap4 i' rmap7 rmap8 e1 c11 c22 => m0 s1' /(valid_state_incl hincl1) hv hext hsao.
  have [s2' [hs1 [hv2 hext2]]]:= Hc1 _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ hv hext hsao.
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

Lemma mapM2_truncate_val_value_uincl tyin vargs1 vargs1' :
  mapM2 ErrType truncate_val tyin vargs1 = ok vargs1' ->
  List.Forall2 value_uincl vargs1' vargs1.
Proof.
Admitted.

Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
Proof.
  move=> s1 m1 s1' ii rs fn args vargs1 vres1 hvargs1 hsem1 Hf hs1'.
  move=> pmap rsp Slots Addr Writable Align rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP=> -[rmap2' i2']; apply: add_iinfoP => /= halloc ? {ii1 ii2} _ ? m0 s2 hvs hext hsao; subst rmap2' i2'.
  move: halloc; rewrite /alloc_call.
  t_xrbindP=> es hcargs [rmap2' rs2] hcres _ /assertP /ZleP hsize _ /assertP /ZleP hmax _ /assertP hle /= ??; subst rmap2' i2.

  (* evaluation of the arguments *)
  have [vargs2 [hvargs2 hargs hdisj haddr]] :=
    alloc_call_argsP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hwf.(wfsl_not_glob) hpmap hvs hcargs hvargs1.

  (*have: extend_mem (emem s1) (emem s3) rip (sp_globs (p_extra P')).
  + split.
    + Search _ rip. admit.
    + case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
      move=> ??.
      apply (eq_mem_source_word hvs).
    + case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
      (* disjoint source? *)
      admit.
    + case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
      admit.
    (* vient de check glob *)
    admit.*)

  (* function call *)
  (* I don't find this inversion elegant, but I think we cannot avoid it. *)
  have [fd1 hfd1]: exists fd, get_fundef P.(p_funcs) fn = Some fd.
  + by inversion_clear hsem1; eexists; eassumption.
    (* TODO: use sem_callE ? *)
  have [fd2 [hfd2 halloc]] := Halloc_fd hfd1.
  move: halloc hfd2; rewrite /alloc_fd.
  t_xrbindP=> {fd2}fd2 _ <- hfd2.
  have halloc_ok: alloc_ok P' fn (emem s2).
  + rewrite /alloc_ok hfd2 => _ [<-] /=.
    split.
    + rewrite /allocatable_stack.
      move: hsao.(wf_sao_size); rewrite /enough_size /allocatable_stack.
      by lia.
    case: is_RAnone => //.
    have := hsao.(wf_sao_align).
    have /vs_top_stack -> := hvs.
    by apply is_align_m.
  have [m2 [vres2 [hsem2 [hext' [hresults hunch]]]]] := Hf _ _ hext hargs hdisj halloc_ok.

  have hvs': valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap1 m0 (with_mem s1 m1) (with_mem s2 m2).
  + case:(hvs) => hvalid hdisj_ hincl hunch_ hrip hrsp heqvm hwfr heqmem hglobv htop.
    split=> //=.
    + move=> ??. rewrite -(sem_call_validw_stable_sprog hsem2). apply hvalid.
    + move=> ??. rewrite -(sem_call_validw_stable_uprog hsem1). apply hdisj_.
    + move=> ?.
      rewrite -(sem_call_validw_stable_uprog hsem1).
      rewrite -(sem_call_validw_stable_sprog hsem2).
      apply hincl.
    + move=> p hvalid1 hvalid2 hdisj__.
      rewrite hunch_ //. 2: rewrite (sem_call_validw_stable_uprog hsem1) //.
      apply (hunch _ hfd1).
      + rewrite (sem_call_validw_stable_sprog hsem2). admit.
      + rewrite (sem_call_validw_stable_uprog hsem1). done.
      rewrite /disjoint_from_writable_params.
      
      (* TODO: better default value ? *)
      apply (nth_Forall3 (a:=None) (b:= {| v_var := pmap.(vrip); v_info := 1%positive |}) (c:=Vbool true)).
      admit.
      admit.
      move=> i hi pi p2 hpi hp2 hw.
      have := Forall3_nth hargs None (Vbool true) (Vbool true) hi.
      rewrite hpi /= hp2.
      move=> [_ [[<-] hargp]].
      have := Forall3_nth haddr None (Vbool true) (Vbool true).
      have [-> _] := Forall3_size haddr.
      have [<- _] := Forall3_size hargs.
      move=> /(_ _ hi).
      have [sr hsr] := Forall2_nth (alloc_call_args_not_None hcargs) None None hi _ hpi.
      move=> /(_ _ _ hsr) [hword hwf'].
      rewrite hp2 in hword.
      move: hword => [?]; subst p2.
      
      
      have hsize_le: size_slot (nth {| v_var := vrip pmap; v_info := 1%positive |} (f_params fd1) i)
        <= size_val (nth (Vbool true) vargs1 i).
      + (* or make a proof on sem_call -> size_of <= size_of *)
        inversion_clear hsem1.
        have := Forall2_nth (mapM2_truncate_val_value_uincl H0) (Vbool true) (Vbool true).
        have [k1 k2] := size_mapM2 H0. rewrite -k2 k1.
        have [<- _] := Forall3_size hargs.
        move=> /(_ _ hi) /value_uincl_subtype /size_of_le.
        apply: Z.le_trans.
        admit. (* hum can we change mem_unchanged_params so that it uses size_val and not size_slot x ? *)

      apply (disjoint_zrange_incl_l (zbetween_le _ hsize_le)).
      apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf.(wfsl_no_overflow) hwf')).
      apply hdisj__.
      apply hwf'.
      rewrite hwf'.(wfr_writable).
      rewrite hw in hsr.
      have /List.Forall_forall := (alloc_call_args_writable hcargs).
      have /InP hin1 := mem_nth None (nth_not_default hsr ltac:(discriminate)).
      move=> /(_ _ hin1 _ hsr). done.

    + case: (hwfr) => hwfsr hval hptr; split=> //.
      + move=> x sr bytes v hgvalid /= hget.
        have [hread hty] := hval _ _ _ _ hgvalid hget.
        split=> //.
        move=> off hmem w /dup[] /get_val_byte_bound hoff ?.
        rewrite -(hunch _ hfd1). (* we could specialize it to hfd1 once and for all *)
        + apply hread => //.
        + rewrite /slot_valid in hvalid.
          have hwf' := check_gvalid_wf hpmap hwfsr hgvalid.
          have /= := hvalid _ _ hwf'.(wfr_slot).
          apply.
          (* hum vraiment pas élégant comme preuve
             en plus j'ai l'impression d'avoir déjà fait cette preuve plein de fois *)
          (* et passer hwf à chaque fois, c'est pénible, on pourrait pas faire cette preuve
             dans stack_alloc_proof.v ? voir de quelles hyps on a besoin *)
          apply (zbetween_trans (zbetween_sub_region_addr hwf.(wfsl_no_overflow) hwf')) => /=.
          apply: between_byte hoff.
          rewrite hty.
          apply (no_overflow_sub_region_addr hwf.(wfsl_no_overflow) hwf').
          rewrite hty.
          apply: zbetween_refl.
        + admit.
        apply: (nth_Forall3 (a:=None)).
        
        rewrite /eq_sub_region_val_read in hread.
        rewrite wf_result_pointer
        
      + move=> x sr.
      
      apply disjoint_zrange_sym.
      apply: disjoint_zrange_U8. done. apply size_slot_gt0.
      apply: no_overflow_incl hargp.(wap_no_overflow).
      apply: zbetween_le. done.
      move=> k hk.
      have HH := hargp.(wap_valid).
      apply: disjoint_range_valid_not_valid_U8.
      wf_arg_pointer mem_unchanged
      Search "U8".
      
      
  have := alloc_call_resP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hpmap _ hcres haddr hresults (s2 := with_mem s2 m2) hs1'.

  (* writing of the returned values *)
  eexists; split.
  + econstructor; try eassumption.
    rewrite P'_globs. done. Search _ write_lval emem. Search _ lv_write_mem. (* lv_write_mem
  alloc_call_resP write_lvals_eq_on

  sem_call
  
  rewrite /wf_results in hrout.
  have := alloc_call_resP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hpmap _ hrs _ (s2 := with_mem s3 m2') hrout hw.
  have: List.Forall
       (λ oi : option nat,
          ∀ (i : nat) (sr : sub_region) (b : bool) (e : pexpr),
            oi = Some i
            → nth (None, Pconst 0) es i = (Some (b, sr), e)
              → nth (Vbool true) vargs' i = Vword (sub_region_addr Addr sr)
                ∧ is_sarr (type_of_val (nth (Vbool true) vargs i)) ∧ wf_sub_region Slots Writable Align sr (type_of_val (nth (Vbool true) vargs i)))
       (sao_return (local_alloc fn)).
  + apply List.Forall_forall. move=> oi /InP /nthP.
    move=> /(_ None) [k h1 h2].
    move=> i sr b e ? hnth; subst oi.
    have := Forall3_nth hRin3 (None, Pconst 0) (Vbool true) (Vbool true) (nth_not_default hnth ltac:(discriminate)).
    rewrite hnth. move=> /(_ _ _ refl_equal) [K [k1 k2]].
    split=> //.
    split=> //.
    admit.
  move=> HH.
  move=> /(_ _ _ _ HH).
  have hvs':
  valid_state pmap glob_size rsp rip Slots Addr Writable Align P rmap1 m0
     (with_mem s1 m2) (with_mem s3 m2').
  + case:(hvs) => hvalid hdisj' hvincl hunch' hrip hrsp heqvm hwfr heqmem.
    split=> //=.
    + move=> s p h1 h2.
      rewrite -(sem_call_validw_stable_sprog hsem). eauto.
    + move=> s p. rewrite -(sem_call_validw_stable_uprog Call). eauto.
    + move=> ?.
      rewrite -(sem_call_validw_stable_sprog hsem).
      rewrite -(sem_call_validw_stable_uprog Call). eauto.
    + move=> ? h1 h2 h3.
      have := hunch.
      rewrite /mem_unchanged_params.
      rewrite -(sem_call_validw_stable_uprog Call) in h2.
      have -> := hunch' _ h1 h2 h3.
      apply. eassumption.
      (* incl m0 (emem s2) ? *) admit.
      done.
      rewrite /disjoint_from_writable_params.
      apply forall_Forall3.
      admit.
      have [_ ?] := Forall3_size hRin; done.
      move=> opi v1 v2 hin1 hin2 hin3.
      rewrite /disjoint_from_writable_param.
      move=> pi p2 ?? hw'; subst opi.
      have /InP /(nthP None) [i hi hnth] := hin1.
      have := Forall3_nth hRin3 (None, Pconst 0) (Vbool true) (Vbool true).
      have -> : size es = size (sao_params (local_alloc fn)).
      + move: hes.
        rewrite /alloc_call_args.
        t_xrbindP=> io jk _ _ <-.
        have [] := size_mapM2 jk. done.
      move=> /(_ _ hi).
      have := Forall2_nth hRin2 None (None, Pconst 0) hi.
      case heq: nth => [bsr e].
      rewrite hnth.
      move=> /(_ _ refl_equal) [sr ?]; subst bsr.
      move=> /(_ _ _ refl_equal) [M1 [M2 M3]].
      have m3: v2 = nth (Vbool true) vargs' i.
      + admit.
      subst v2.
      rewrite M1 in m3.
      case: m3=> ->.
      have ?: v1 = nth (Vbool true) vargs i.
      have:= (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf.(wfsl_no_overflow) M2)).
      have := hdisj'.
      rewrite /disjoint_source.
      rewrite /sub_region_addr.
      Search valid_state.
(*       have := Forall3_forall hRin hinn. *)
      case: opi hinn => [pi|//] hinn. (*
      move=> [p [????[??]]]; subst v2.
      simpl. move=> _ [<-].
      move=> hrinn. *)
      (* implied by h3 *) admit.
    + case: (hwfr) => hwfsr hval hptr; split=> //.
      + move=> y sry bytesy vy hgvalidy hgety.
        have [hread hty] := hval _ _ _ _ hgvalidy hgety.
        split=> //.
        move=> off hmem w hgett /=.
        move: hread => /(_ off hmem w hgett) <-.
        symmetry.
        rewrite /mem_unchanged_params in hunch.
        apply (hunch _ hfd).
        have /= hwfy := check_gvalid_wf hpmap (wfr_wf (wf_rmap := hwfr)) hgvalidy.
        apply (hvalid _ _ hwfy.(wfr_slot)).
        have hjk := zbetween_sub_region_addr hwf.(wfsl_no_overflow) hwfy.
        apply: (between_byte _ hjk).
        apply (no_overflow_sub_region_addr hwf.(wfsl_no_overflow) hwfy).
        have := get_val_byte_bound hgett. rewrite hty. done.
        (* a-t-on déjà fait des preuves similaires dans stack_alloc_proof ? Je pense. *)
        have /= hwfy := check_gvalid_wf hpmap (wfr_wf (wf_rmap := hwfr)) hgvalidy.
        move=> contra.
        have := hdisj' _ _ hwfy.(wfr_slot) contra.
        apply zbetween_not_disjoint_zrange.
        have hjk := zbetween_sub_region_addr hwf.(wfsl_no_overflow) hwfy.
        apply: (between_byte _ hjk).
        apply (no_overflow_sub_region_addr hwf.(wfsl_no_overflow) hwfy).
        have := get_val_byte_bound hgett. rewrite hty. done.
        done.
        rewrite /disjoint_from_writable_params.
        admit.
      + move=> y sry /hptr [pky [hly hpky]].
        exists pky; split=> //.
        case: pky hly hpky => //.
        move=> s ofs ws z f hly /=. move=> hjk /hjk <-.
        symmetry.
        (* il faut revenir à 8 bits *)
(*         apply hunch. *)
        (* cf. eq_read (and simplify eq_mem_source_word) *)
        apply eq_read. move=> i hi. rewrite addE.
        admit.
      + move=> p ?.
        apply hext'.(em_read_old8). done.
    rewrite -(sem_call_stack_stable_sprog hsem).(ss_top_stack). done.
  move=> /(_ _ _ hvs').
  move=> [s3' [hw3 hvs3]].
  eexists. split.
  econstructor. rewrite P'_globs. eassumption. eassumption.
  rewrite P'_globs. eassumption.
  split=> //.
  Search _ extend_mem valid_state.
  have /= := valid_state_extend_mem hwf hvs' hext' hvs3.
  apply.
  apply (write_lvals_validw hw).
  apply (write_lvals_validw hw3). *)
Admitted.

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

Lemma nth_alt A a (l : list A) n :
  nth a l n = List.nth n l a.
Proof. elim: l n => [|x l ih]; by case. Qed.

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

Lemma value_uincl_wf_result_pointer m vargs1 vargs2 i vr1 vr1' p :
  value_uincl vr1' vr1 ->
  wf_result_pointer m vargs1 vargs2 i vr1 p ->
  wf_result_pointer m vargs1 vargs2 i vr1' p.
Proof.
  move=> huincl [hargs hsize hread].
  have hle := size_of_le (value_uincl_subtype huincl).
  split=> //.
  + by lia.
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
Lemma write_vars_size_le A (l:seq (option A)) params :
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
  move=> _ /to_arrI [n' [_ [-> /WArray.cast_len /ZleP]]] /=.
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
  case: (hresultp) => hrargs hsize hread.
  split=> //.
  + by rewrite (Forall3_nth hptreq None (Vbool true) (Vbool true)
      (nth_not_default hpi ltac:(discriminate)) ltac:(congruence)).
  have := Forall2_nth hincl (Vbool true) (Vbool true).
  have -> := Forall2_size hincl.
  have [<- _] := Forall3_size hargs.
  move=> /(_ _ (nth_not_default hpi ltac:(discriminate))).
  move=> /value_uincl_subtype /size_of_le.
  by apply Z.le_trans.
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
  case: (hresultp) => hrargs hsize hread.
  split=> //.
  move=> off w /dup[] /get_val_byte_bound hoff.
  rewrite -hfss.(fss_read_old8); first by apply hread.
  have := Forall3_nth hargs None (Vbool true) (Vbool true) (nth_not_default hpi ltac:(discriminate)).
  rewrite hpi /= hrargs.
  move=> [_ [[<-] hargp]].
  rewrite -hvalid.
  apply hargp.(wap_valid).
  apply: between_byte hoff.
  + by apply (no_overflow_incl (zbetween_le _ hsize) hargp.(wap_no_overflow)).
  by apply: zbetween_le hsize.
Qed.

(* TODO: choose a better name *)
Lemma value_uincl_disjoint_from_writable_params fn vargs2 vargs2' p params :
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2' ->
  disjoint_from_writable_params fn p params vargs2 ->
  disjoint_from_writable_params fn p params vargs2'.
Proof.
  move=> hptreq.
  rewrite /disjoint_from_writable_params.
  elim: {vargs2 vargs2'} hptreq params => //.
  move=> opi varg2 varg2' sao_params vargs2 vargs2' hptreq _ ih [|x params] hdisj;
    inversion_clear hdisj.
  constructor; last by apply ih.
  move=> pi p2 ?? hw; subst opi varg2'.
  move: hptreq => /(_ ltac:(discriminate)) ?; subst varg2.
  by eauto.
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
    case: is_RAnone hal hmax => [_|->] hmax; last by apply /ZleP; lia.
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

  have hsize_le := write_vars_size_le (init_params_sarr hparams) hs1. (* 'backported' from write_vars of args *)
  (* TODO:
     - extend_mem implies no_overflow, duplicate! -> maybe we can move no_overflow hyp in LOCAL section
     - disjoint_zrange rsp rip implies no_overflow rip et no_overflow rsp, duplicates!
  *)
  have /= hvs := init_stk_state_valid_state hlayout hover hdisj_glob_locals
    hargs' hsize_le hlocal_map hparams hext hass refl_equal rip_rsp_neq.
  have hpmap := init_params_wf_pmap hlayout rsp vargs1' vargs2' hlocal_map hparams.
  (* TODO: [vrip] appears only because we need a default value in [get_pi_nth].
     It does not seem very clean to me.
  *)
  have hslots := Hwf_Slots hlayout hover hdisj_glob_locals hext.(em_align)
    hass.(ass_align_stk) hargs' hdisjv' hsize_le (p_extra P').(sp_rip) hparams hdisj_locals_params.

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
      rewrite (top_stack_after_aligned_alloc _ hok2).
      rewrite wunsigned_add; first by lia.
      split; first by lia.
      assert (hrange := wunsigned_range (top_stack m2)).
      have [? _] := round_ws_range (sao_align (local_alloc fn)) (sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)).
      by lia.
   by apply hass.(ass_align_stk).

  (* execution of the body *)
  (* TODO: hext''' can be deduced from valid_state_extend_mem, is it really needed ? *)
  have [s2' [hsem2 [hvs''' hext''']]] := Hc _ _ _ _ _ _ _ _ _ hpmap hslots _ halloc _ _ hvs' hext'' hsao.

  (* get_var of results *)
  have harr: List.Forall2 (fun osr (x : var_i) => osr <> None -> is_sarr (vtype x)) (map fst alloc_params) (f_params fd).
  + by apply: (Forall2_trans _ (init_params_alloc_params_not_None hparams) (init_params_sarr hparams)); auto.
  have hsize_le' := write_vars_size_le harr hs1.
  have haddr := init_params_alloc_params rsp hargs'' hparams.
  have [vres2 [hvres2 hresults]] := check_resultsP hvs''' hsize_le' haddr hcresults hvres1.

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
  rewrite /mem_unchanged_params hfd.
  move=> _ [<-] p hvalid1 hvalid2 hdisjp.
  rewrite -hfss.(fss_read_old8) -?hvalideq2 //.
  have /vs_unchanged := hvs'''; apply => //.
  + by rewrite -hvalideq1.
  apply (disjoint_from_writable_params_all_slots hlayout hover hdisj_glob_locals hargs'' P'.(p_extra).(sp_rip) hparams).
  + by apply (value_uincl_disjoint_from_writable_params hptreq hdisjp).
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

(*
Variable locals' : Mvar.t ptr_kind.
Variable rmap : region_map.
Variable vnew' : Sv.t.

Definition pmap := .

Definition Slots :=
  Sv.union (Mvar.fold (fun s _ acc => Sv.add s acc) globals' Sv.empty)
           (Mvar.fold (fun s _ acc => Sv.add s acc) stack Sv.empty).

Definition Align s :=
  match Mvar.get globals' s, Mvar.get locals' s with
  | Some (_, ws), _ => ws
  | _, Some pk =>
    match pk with
    | Pdirect _ _ ws _ _ => ws
    | Pregptr _ => U8
    | Pstkptr _ _ ws _ _ => ws
    end
  | _, _ => U8
  end.

Definition Addr (s : slot) : u64 := 0.
Definition Writable (s : slot) :=
  match Mvar.get globals' s with
  | Some _ => false
  | _ => true
  end.
*)

(*
End INIT.

Section PROC.

Hypothesis p_extra : sprog_extra.

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].
Variable (m0:mem).
Variable (local_alloc : funname -> stk_alloc_oracle_t).
Variable (P: uprog) (ev: extra_val_t (progT := progUnit)).
Notation gd := (p_globs P).
Hypothesis test : forall fn fd,
  (* ou juste In f P.(p_funcs) ? *)
  get_fundef P.(p_funcs) fn = Some fd ->
  exists fd',
  get_fundef P'.(p_funcs) fn = Some fd' /\
  alloc_fd p_extra mglob local_alloc (fn, fd) = ok (fn, fd').
(* TODO: à remplacer par alloc_proc P = ok P' *)
  
Variables (rsp: ptr).
(*
Let Pc s1 (c1:cmd) s2 := forall pmap Slots Addr (Writable : slot -> bool) Align
  (addr_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s))
  (disjoint_writable : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
    Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2))
  (slot_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s)),
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  forall rmap1 rmap2 c2, fmapM (alloc_i pmap local_alloc) rmap1 c1 = ok (rmap2, c2) ->
  forall s1', valid_state pmap rip rsp Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  exists s2', sem (sCP:= sCP_stack) P' rip s1' c2 s2' /\
    valid_state pmap rip rsp Slots Addr Writable Align P rmap2 m0 s2 s2'.
*)
(* TODO: mettre tout le raisonnement sur sem_Ind_* en dehors de la 1ère section
   Créer un prédicate wf_slot ? *)
Let Pi_r s1 (i1:instr_r) s2 :=
  forall pmap rmap1 rmap2 ii1 ii2 i2, alloc_i pmap local_alloc rmap1 (MkI ii1 i1) = ok (rmap2, MkI ii2 i2) ->
  forall Slots Addr (Writable : slot -> bool) Align
  (addr_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s))
  (disjoint_writable : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
    Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2))
  (slot_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s)),
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  forall s1', valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  exists s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2'.

Let Pi s1 (i1:instr) s2 :=
  forall pmap rmap1 rmap2 i2, alloc_i pmap local_alloc rmap1 i1 = ok (rmap2, i2) ->
  forall Slots Addr (Writable : slot -> bool) Align
   (addr_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s))
  (disjoint_writable : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
    Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2))
  (slot_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s)),
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  forall s1', valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  exists s2', sem_I (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall pmap rmap1 rmap2 c2, fmapM (alloc_i pmap local_alloc) rmap1 c1 = ok (rmap2, c2) ->
  forall Slots Addr (Writable : slot -> bool) Align
   (addr_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s))
  (disjoint_writable : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
    Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2))
  (slot_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s)),
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  forall s1', valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  exists s2', sem (sCP:= sCP_stack) P' rip s1' c2 s2' /\ valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2'.

Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.


Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) :=
  forall (* fd *) pmap rmap1 rmap2 ini res args i2,
(*   get_fundef (p_funcs P) fn = Some fd → (* from merge_varmaps_proof *) *)
  alloc_call pmap local_alloc rmap1 ini res fn args = ok (rmap2, i2) ->
(*   fmapM (alloc_i pmap local_alloc) rmap1 fd.(f_body) = ok (rmap2, i2) -> *)
  forall vm1 s1' s2 Slots Addr Writable Align,
  let: s1 := {| evm := vm1; emem := m1 |} in
  valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  sem_pexprs gd s1 args = ok vargs ->
  write_lvals gd (with_mem s1 m2) res vres = ok s2 ->
  exists s2', sem_i (sCP := sCP_stack) P' rip s1' i2 s2'
    /\ valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2'.

  Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
  Proof.
    rewrite /sem_Ind_proc /=.
    move=> m1 m2 fn f vargs vargs' s0 s1 s2 vres vres'.
    move=> hf hvargs [<-] hs1 ? Hc hvres hvres' ->.
    rewrite /Pfun.
    move=> pmap rmap1 rmap2 ini res args i2 hcall vm1 s1' s3
      Slots Addr Writable Align hvs hvargs' hs3.
    move: hcall.
    rewrite /alloc_call.
    t_xrbindP=> es hargs [rmap3 rs] hres <- <-.
    have [fd' [hf']] := test hf.
    rewrite /alloc_fd.
    t_xrbindP=> fd1.
    rewrite /alloc_fd_aux.
    t_xrbindP=> -[[locals rmap] vnew] hinit.
    t_xrbindP=> -[[[vnew2 lmap] rmap4] alloc_params] hinitparams.
    t_xrbindP=> -[rmap5 i5]. apply: add_finfoP.
    move=> halloc hres2 hfd'.
    move: Hc. rewrite /Pc.
    move=> /(_ _ _ _ _ halloc).
    move: hinit; rewrite init_local_map_eq.
    t_xrbindP.
    move=> [stack size] hlayout hinit.
    Memory.alloc_stack_complete
    have := Haddr_no_overflow hlayout.
    move=> /(_ (top_stack (emem s1))).
    Search _ top_stack.
    move=> ??.
    eexists; split.
    + simpl. econstructor. admit. econstructor. eassumption.
      admit. simpl. rewrite /init_stk_state. Memory.alloc_stack_spec admit. admit.
(*     move: halloc. *)
(*     move=> /(_ _ _ _ _ _ _ _ _ halloc). *)
  Admitted.

  Lemma check_cP s1 c s2: sem P ev s1 c s2 -> Pc s1 c s2.
  Proof.
    have := @sem_Ind _ _ _ P ev Pc Pi_r Pi Pfor Pfun.
    apply.
    + move=> s pmap rmap1 rmap2 c2 halloc Slots Addr Writable Align h1 h2 h3 h4.
      move=> s1' hvs.
      apply: Hskip; try eassumption.
    + move=> ????????????????????????.
      apply: Hcons; eauto.
    + move=> ?????????????????????.
      apply: HmkI; eauto.
    + move=> ????????????????????????????.
      apply: Hassgn; eauto.
    + move=> ????????????????????????.
      apply: Hopn; eauto.
    + move=> ?????????????????????????.
      apply: Hif_true; eauto.
    + move=> ?????????????????????????.
      apply: Hif_false; eauto.
    + move=> ????????????????????????????????.
      apply: Hwhile_true; eauto.
    + move=> ??????????????????????????.
      apply: Hwhile_false; eauto.
    + done.
    + done.
    + done.
    + move=> ??????????????????????????????.
      apply: Hcall; eauto.
    apply Hproc.
  Qed.

End PROC.

End FUN.

(*


Variable (P': sprog).
Variable (rip : ident).
Variable (global_data : seq u8).
Variable (global_alloc : seq (var * wsize * Z)).
Variable (local_alloc : funname -> stk_alloc_oracle_t).

Variable mglob : Mvar.t (Z * wsize).
Hypothesis hmglob : init_map (Z.of_nat (size global_data)) global_alloc = ok mglob.

Hypothesis halloc : alloc_prog rip global_data global_alloc local_alloc P = ok P'.

Lemma halloc_fd : forall fn fd,
  get_fundef P.(p_funcs) fn = Some fd ->
  exists fd', get_fundef (p_funcs P') fn = Some fd' /\
              alloc_fd P'.(p_extra) mglob local_alloc (fn, fd) = ok (fn, fd').
Proof.
  move: halloc; rewrite /alloc_prog hmglob /=.
  case: eqP => // _.
  case: ifP => // _.
  t_xrbindP=> l hl <- /=.
  elim: P.(p_funcs) l hl => //=.
  move=> [fn fd] p_funcs ih.
  t_xrbindP=> _ [fn' fd'] hfd' l' hl' <-.
  have ?: fn' = fn; last subst fn'.
  + by move: hfd'; rewrite /alloc_fd; t_xrbindP.
  move=> fn1 fd1.
  case: eqP => /=.
  + by move=> -> [<-]; exists fd'; rewrite eq_refl.
  move=> hneq hfd1.
  have [fd1' [??]] := ih _ hl' _ _ hfd1.
  exists fd1'.
  by have /eqP /negPf -> := hneq.
Qed.

*)

(*
Definition valid_map1 (m:Mvar.t Z) (size:Z) :=
  forall x px, Mvar.get m x = Some px -> 
     exists sx, size_of (vtype x) = ok sx /\
     [/\ 0 <= px, px + sx <= size,
      aligned_for (vtype x) px &
         forall y py sy, x != y -> 
           Mvar.get m y = Some py -> size_of (vtype y) = ok sy ->
           px + sx <= py \/ py + sy <= px].

Lemma init_mapP l sz m :
  init_map sz l = ok m -> 
  valid_map1 m sz.
Proof.
  rewrite /init_map.
  set f1 := (f in foldM f _ _ ).
  set g := (g in foldM _ _ _ >>= g). 
  have : forall p p',
    foldM f1 p l = ok p' -> 
    valid_map1 p.1 p.2 -> 0 <= p.2 ->
    (forall y py sy, Mvar.get p.1 y = Some py ->
        size_of (vtype y) = ok sy -> py + sy <= p.2) ->
    (p.2 <= p'.2 /\ valid_map1 p'.1 p'.2).
  + elim:l => [|[v pn] l Hrec] p p'//=.
    + by move=>[] <- ???;split=>//;omega.
    case:ifPn=> //= /Z.leb_le Hle.
    case: ifP => // Hal.
    case Hs : size_of=> [svp|]//= /Hrec /= {Hrec}Hrec H2 H3 H4. 
    have Hpos := size_of_pos Hs.
    case:Hrec.
    + move=> x px;rewrite Mvar.setP;case:ifPn => /eqP Heq.
      + move=> [] ?;subst;exists svp;split=>//;split => //.
        + omega. + omega.
        move=> y py sy Hne.
        by rewrite Mvar.setP_neq // => /H4 H /H ?;omega.
      move=> /H2 [sx] [Hsx] [] Hle0 Hpx Hal' Hy;exists sx;split=>//;split=>//.
      + omega.
      move=> y py sy Hne;rewrite Mvar.setP;case:eqP=> [?[]? |].
      + subst;rewrite Hs => -[] ?;subst; omega.
      by move=> Hney;apply Hy.
    + omega.
    + move=> y py sy;rewrite Mvar.setP;case:eqP=> [?[]?|].
      + subst;rewrite Hs => -[] ->;omega.
      move=> ? /H4 H /H ?;omega.
    move=> Hle2 H';split=>//;first by omega.
  move=> H;case Heq : foldM => [p'|]//=.
  case: (H _ _ Heq)=> //= Hp' Hv.
  rewrite /g; case:ifP => //= /Z.leb_le Hp [<-].
  move=> x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3 H4.
  by exists sx;split=>//;split=>//;omega.
Qed.
*) *)

Lemma getfun_alloc nrsp glob_data oracle oracle_g (P:uprog) (SP:sprog) :
  alloc_prog nrsp glob_data oracle oracle_g P = ok SP ->
  exists lg mglob, 
    [/\ init_map (Z.of_nat (size SP.(p_extra).(sp_globs))) lg = ok mglob,
        check_globs (p_globs P) mglob SP.(p_extra).(sp_globs) &
        forall fn fd,
        get_fundef (p_funcs P) fn = Some fd ->
        exists fd', 
           get_fundef SP.(p_funcs) fn = Some fd' /\
           alloc_fd SP.(p_extra) mglob oracle_g (fn, fd) = ok (fn,fd')].
Proof.
  rewrite /alloc_prog.
(*   case: (oracle_g P) => -[data rip] l. *)
  t_xrbindP => mglob; apply: add_err_msgP => heq.
  case: eqP => // ?.
  case heq1: check_globs => //; t_xrbindP => sfd hm ?; subst SP => /=.
  exists oracle, mglob;split => //.
  elim: (p_funcs P) sfd hm => [ | [fn1 fd1] fs hrec sfd] //=.
  t_xrbindP => -[fn2 fd2] H fd2' H0 ?; subst sfd.
  have ?: fn2 = fn1; last subst fn2.
  + move:H; rewrite /alloc_fd; t_xrbindP; done.
  move=> fn3 fd3.
  case: eqP.
  + move=> -> [<-]. exists fd2. split. by rewrite /= eq_refl.
    done.
  move=> ? /hrec -/(_ _ H0) [? [??]].
  eexists; split; try eassumption.
  rewrite /=.
  case: eqP => //.
Qed.

Lemma all_In (T:Type) (P: T -> bool) (l:seq T) x :
  all P l ->
  List.In x l -> P x.
Proof. by elim: l => //= x' l hi /andP [] hp /hi h -[<- | /h]. Qed.

(*
Lemma valid_top (P : uprog) nrsp (stk_size : Z) (rsp : u64) (glob_size : Z) 
         (rip : u64) (data : seq u8) (gm : gmap) (sm : smap) 
         s1 s2 :
         valid P nrsp stk_size rsp glob_size rip data gm sm s1 s2 ->
 top_stack (emem s2) = rsp.
Proof.
  by move=> /valid_top_frame; rewrite /top_stack; case: frames => //= ?? [->].
Qed.

Lemma alloc_prog_stk_id nrsp oracle oracle_g P SP :
  alloc_prog nrsp oracle oracle_g P = ok SP →
  sp_stk_id SP.(p_extra) = nrsp.
Proof.
  by rewrite /alloc_prog; case: (oracle_g _) => - []; t_xrbindP => ?????; case: ifP => // _; t_xrbindP => ?? <-.
Qed. *)

Definition n := 0.


Lemma alloc_fdP nrsp glob_data oracle oracle_g (P:uprog) SP fn fd fd':
  alloc_prog nrsp glob_data oracle oracle_g P = ok SP ->
  get_fundef (p_funcs P) fn = Some fd ->
  get_fundef (p_funcs SP) fn = Some fd' ->
  forall ev m1 va m1' vr rip, 
    sem_call P ev m1 fn va m1' vr ->
    forall m2, extend_mem m1 m2 rip SP.(p_extra).(sp_globs) ->
(*     (exists p, alloc_stack m2 (sf_stk_sz fd'.(f_extra)) = ok p) -> *)
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(p_extra).(sp_globs) /\
      sem_call (sCP:=sCP_stack) SP rip m2 fn va m2' vr'.
Proof.
  move=> hap get Sget. 
(*   have ? := alloc_prog_stk_id hap; subst nrsp. *)
  
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc hap.
  have [fd1 [] {hf}]:= hf _ _ get.
  rewrite Sget => -[?];subst fd1.
  rewrite /alloc_fd /alloc_fd_aux.
(*   case: (oracle (fn, fd)) => -[stk_size lv] ptrreg_of_reg . *)
  t_xrbindP => fd1 [[pmap rmap] vnew] hinit.
  t_xrbindP=> -[[[vnew2 pmap2] rmap2] res].
  apply: add_err_funP.
  move=> hinit2.
  t_xrbindP=> -[rmap3 c].
  apply: add_finfoP=> hc.
  t_xrbindP=> vres.
  apply: add_err_funP => hres.
  move=> ??; subst fd1 fd'. (*
  
  t_xrbindP.
  
   mstk ?; subst fd'. rewrite /add_err_fun.
  case histk : init_map => [mstk1 | //] [?]; subst mstk1.
  set gm := {| rip := _ |}; set sm0 := {| mstk := _ |}.
  move=> sm1; case hfold : foldM => [sm1' | //] [?]; subst sm1'.
  move=> [sme c]; apply: add_finfoP => hc /=.
  case: andP => // -[] hneq hres [?] ?;subst fd1 fd' => /=. *)
  move=> ev m1 vargs m1' vres' rip hcall m2 hm2.
  pose glob_size := Z.of_nat (size (sp_globs SP.(p_extra))).
(*  have Hstk: ptr_ok (top_stack m2s) stk_size.
  + by move: ha=> /Memory.alloc_stackP [].
  have Hglob: ptr_ok rip (Z.of_nat (size (sp_globs SP.(p_extra)))).
  + by rewrite /ptr_ok; case hm2. *)
(*
  have hv : valid_map gm sm0 stk_size glob_size.
  + rewrite /sm0 => x mpx; rewrite /find_gvar /=; case:ifP => his.
    + rewrite Mvar.mapP; case heq: Mvar.get => [ofsx | // ] [?]; subst mpx.
      have [sx [h1 [h2 h3 h4 h5]]] := init_mapP histk heq.
      exists sx;split => //; split => //.
      move=> y mpy sy; case: ifP => his'.
      + rewrite  Mvar.mapP; case heq': Mvar.get => [ofsy | // ] [?]; subst mpy => /=.
        move=> hsy _; case: (v_var (gv x) =P gv y).
        + by move => heq1; move: heq'; rewrite -heq1 heq => -[->]; rewrite eq_refl.
        move=> /eqP => heq1; have := h5 _ _ _ heq1 heq' hsy; case: eqP => //.
        by have := size_of_pos h1; have := size_of_pos hsy; lia.
      by case: Mvar.get => [ofsy | //] [<-].
    case heq: Mvar.get => [ofsx' | // ] [?]; subst mpx => /=.
    have [sx [h1 [h2 h3 h4 h5]]] := init_mapP higlob heq.
    exists sx;split => //; split => //.
    move=> y mpy sy; case: ifP => his'.
    + by rewrite  Mvar.mapP; case heq': Mvar.get => [ofsy | // ] [?]; subst mpy.
    case heq': Mvar.get => [ofsy | //] [?] hsy _; subst mpy => /=.
    case: (v_var (gv x) =P gv y).
    + by move => heq1; move: heq'; rewrite -heq1 heq => -[->]; rewrite eq_refl.
    move=> /eqP => heq1; have := h5 _ _ _ heq1 heq' hsy; case: eqP => //.
    by have := size_of_pos h1; have := size_of_pos hsy; lia. *)
  have heq_init :
  exists m2s,
    init_state (semCallParams := sCP_stack) {|
    sf_align := sao_align (oracle_g fn);
    sf_stk_sz := sao_size (oracle_g fn);
    sf_stk_extra_sz := sao_extra_size (oracle_g fn);
    sf_stk_max := sao_max_size (oracle_g fn);
    sf_to_save := sao_to_save (oracle_g fn);
    sf_save_stack := sao_rsp (oracle_g fn);
    sf_return_address := sao_return_address (oracle_g fn) |}
    
    (* {| sf_stk_sz := stk_size; sf_extra := ptrreg_of_reg |} *)
                          SP.(p_extra) rip {| emem := m2; evm := vmap0 |} = 
    ok {| emem := m2s; evm := vmap0.[x86_variables.var_of_register RSP <- ok (pword_of_word (top_stack m2s))]
                                             .[{| vtype := sword64; vname := sp_rip (p_extra SP) |} <- ok (pword_of_word rip)] |}.
  + rewrite /init_state /= /init_stk_state /=.
    have := @Memory.alloc_stack_complete m2 (sao_align (oracle_g fn)) (sao_size (oracle_g fn)) (sao_extra_size (oracle_g fn)).
    case.
    + apply /and3P. split.
      + move: hinit. rewrite /init_local_map.
        t_xrbindP=> -[??] /init_stack_layoutP [? _].
        case: ifP => //.
        rewrite Zcmp_le => /ZleP /= ?.
        move=> _. apply /ZleP. lia.
      + admit.
      admit.
    move=> m2s hm2s. exists m2s. rewrite hm2s /=.
    f_equal. apply f_equal. f_equal.
    f_equal. rewrite /pword_of_word. f_equal. f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
    rewrite /pword_of_word. f_equal. f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
    
  have hvalid : 
    valid P (sp_stk_id SP.(p_extra)) stk_size (top_stack m2s) 
            (Z.of_nat (size (sp_globs SP.(p_extra)))) rip (sp_globs SP.(p_extra)) gm sm0
              {| emem := m1; evm := vmap0 |}
              {| emem := m2s; evm := vmap0.[vrsp (sp_stk_id SP.(p_extra)) <- ok (pword_of_word (top_stack m2s))]
                                             .[vrip gm <- ok (pword_of_word rip)] |}.
  + case: hm2 => halign2 hread_eq hdisj hval hglob.
    have [hin hread_eqs hvals hal hdisjs htopf]:= Memory.alloc_stackP ha.
    constructor => //=.
    + move=> w sz hw; split; last by apply hdisj.
      by have := hdisjs w sz; rewrite hval hw /= => /(_ erefl) -[] h; apply /negP /nandP;
        [left|right];apply /ZltP; lia.
    + by move=> w sz hw; rewrite (hread_eq _ _ hw) hread_eqs // hval hw.
    + by move=> w sz; rewrite hvals hval -orbA (orbC (_ && _)) orbA.
(*    + by move=> x hnin hnrsp hnrip;rewrite !Fv.setP_neq // eq_sym. *)
    + by rewrite /get_var Fv.setP_eq.
    + rewrite /get_var Fv.setP_neq ? Fv.setP_eq //.
      by apply/eqP => -[k]; move/eqP: hneq; rewrite k.
    + by rewrite htopf. 
    + move=> x; rewrite /find_gvar.
      case: ifP => his. 
      + rewrite Mvar.mapP; case heq: Mvar.get => [ofs /=| //];split => //.
        have := init_mapP histk heq. 
        case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
        + move=> off hoff; rewrite hvals; split.
          + apply /orP; right; rewrite is_align8 andbT.
            rewrite /between wsize8 /ptr_size /wptr /= (wunsigned_rsp_add Hstk); [ | nia | nia ].
            by apply/andP; split; apply/ZleP; nia.
          move=> s' a; rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype /= => hok.
          by have /Varr_inj [e ?]:= ok_inj hok; subst s' a; rewrite WArray.get0.
        split.
        + rewrite hvals; apply /orP; right.
          have heq2 : v_var (gv x) = {| vtype := sword sz; vname := vname (gv x) |}.
          + by case: (v_var (gv x)) Htype => /= ?? ->.
          rewrite heq2 in heq. have /(_ sz (vname (gv x)) ofs):= valid_get_w Hstk Hglob hv. 
          by rewrite /sm0 /= Mvar.mapP heq /= /wptr /= => /(_ erefl).
        by move=> ?;rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype.
      rewrite /gm /=; case heq: Mvar.get => [ofs /=| //]; split => //.
      have := init_mapP higlob heq. 
      case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
      + move=> off hoff; rewrite hvals.
        have hvalid : validw m2 (wptr (top_stack m2s) rip MSglob + wrepr U64 (off + ofs)) U8.
        + rewrite hval; apply /orP; right; rewrite is_align8 andbT.
          rewrite /between wsize8 /ptr_size /wptr (wunsigned_rip_add Hglob).
          + by apply/andP; split; apply/ZleP; nia.
          + nia.
          by move: (size _) hoff h2 h1; clear=> *;lia. 
        split; first by rewrite hvalid.
        move=> s' a; rewrite /get_gvar his /get_global /get_global_value.
        case heq1 : xseq.assoc => [ []//= | //]; case: eqP => //.
(*
        rewrite Htype => -[?] heq2; subst n'; have /Varr_inj [e ?] := ok_inj heq2; subst n a => /=.
        have := all_In hcheck (xseq.assoc_mem' heq1).
        rewrite /check_glob /= heq => /andP [hle /allP hall] v hget. 
        have := hall (Z.to_nat off); rewrite mem_iota /= Z2Nat.id; last by lia.
        rewrite hget.
        match goal with |- (?A -> _) -> _ => have hh: A end.
        + by apply /ltP; case: hoff => ? /Z2Nat.inj_lt;apply.
        move=> /(_ hh) {hh} /eqP <-.
        rewrite /wptr -hread_eqs;last by move: hvalid; rewrite /wptr /=.
        rewrite hglob; last by lia. 
        rewrite Z.add_comm Z2Nat.z2nD;first last.
        + by apply /lezP;rewrite -ssrring.z0E;lia.
        + by apply /lezP;rewrite -ssrring.z0E;lia. 
        by rewrite -nth_drop wrepr0. *)
      rewrite /valid_ptr_word /get_gvar /wptr his.
      have hvalid : validw m2 (rip + wrepr U64 ofs) sz.
      + rewrite hval; apply /orP; right.
        case: halign2 => hh1 hh2; rewrite /between hh2 h3 andbT.
        rewrite (wunsigned_rip_add Hglob) //.
        + apply /andP;split; apply /ZleP;lia.
        move: (size _) (@wsize_size_pos sz) h2 => *; lia. 
      rewrite hvals hvalid;split => // v. 
      rewrite -hread_eqs // /get_global /get_global_value Htype.
      case heq1 : xseq.assoc => [[ sz' w] //= | //]; case: eqP => // -[?] [?]; subst sz' v.
      exists w => //; rewrite Memory.readP /CoreMem.read.
      have := validr_validw m2 (rip + wrepr U64 ofs)%R sz.
      rewrite hvalid => /is_okP => -[? ->] /=.
      have := all_In hcheck (xseq.assoc_mem' heq1).
Opaque Z.to_nat.
      rewrite /check_glob heq /= => /andP [hh1 /eqP hh2];subst w.
      f_equal; f_equal.
      rewrite /CoreMem.uread; apply: (@eq_from_nth _ (wrepr U8 0)).
      have hw := @le0_wsize_size sz.
      + rewrite size_map size_ziota size_take size_drop.
        case: ifPn => // /ltP; rewrite Nat2Z.inj_lt Z2Nat.id // Nat2Z.n2zB; last first. 
        rewrite -(Nat2Z.id (size _)); apply /leP; rewrite -Z2Nat.inj_le; lia.
        rewrite -subZE Z2Nat.id // => hh. 
        have -> : (wsize_size sz) = Z.of_nat (size (sp_globs SP.(p_extra))) - ofs.
        + by move:(size _) h2 hh => *; lia.
        by rewrite Z2Nat.inj_sub // Nat2Z.id.
      move=> i; rewrite size_map size_ziota => hi.
      rewrite (nth_map 0) ?size_ziota // nth_take // nth_drop nth_ziota // Memory.addP /=.
      rewrite -GRing.addrA -wrepr_add.
      move /ltP: hi; rewrite Nat2Z.inj_lt Z2Nat.id // => hi.
      have : 0 <= ofs + Z.of_nat i ∧ ofs + Z.of_nat i < Z.of_nat (size (sp_globs SP.(p_extra))).
      + by move:(size _) h2 => *; lia.
      move=> /hglob; rewrite Memory.readP /CoreMem.read CoreMem.uread8_get. 
      t_xrbindP => ?? ->; rewrite Z2Nat.inj_add //; last by apply Zle_0_nat.
      by rewrite Nat2Z.id addP.
    move=> i [hi1 hi2]; rewrite -hread_eqs; first by apply hglob.
    rewrite hval is_align8 andbT;apply /orP;right.
    apply /andP;rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP; lia.
Transparent Z.to_nat.
  inversion_clear hcall.
  case: H1 (* init_state ... *) => ?;subst s0.
  move: H;rewrite get => -[?];subst f.
  have uvargs0 : List.Forall2 value_uincl vargs0 vargs0.
  + by apply List_Forall2_refl.
  have [s1' [hwargs hvalid2 ]] := check_lvarsP hvalid hfold uvargs0 H2.
  have hdisj : 0 < stk_size -> 0 < Z.of_nat (size (sp_globs SP.(p_extra))) ->
       ((wunsigned (top_stack m2s) + stk_size <=? wunsigned rip)
                || (wunsigned rip + Z.of_nat (size (sp_globs SP.(p_extra))) <=? wunsigned (top_stack m2s))).
  + case: hm2 =>  _ _ _ hvm2 _ hss hsg. 
    have [_ _ _ _ hh _]:= Memory.alloc_stackP ha.
    have /hh : validw m2 rip U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between Z.leb_refl /= wsize8; apply /ZleP. 
      by move: (size _) hsg => *;lia.
    have /hh : validw m2 (rip + wrepr Uptr (Z.of_nat (size (sp_globs SP.(p_extra))) - 1)) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between (wunsigned_rip_add Hglob); [ | lia | lia]. 
      by rewrite wsize8; apply /andP; split; apply /ZleP; by move: (size _) hsg => *; lia.
    rewrite wsize8 (wunsigned_rip_add Hglob); [ | lia | lia]. 
    move=> a1 a2;apply /orP.
    rewrite /is_true !Z.leb_le. 
    case: a1; first by lia.
    case: a2; last by lia.
    move=> h_1 h_2.
    have u1 : stk_size < Z.of_nat (size (sp_globs SP.(p_extra))) by lia.
    have /hh : validw m2 (top_stack m2s) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between wsize8; apply /andP.
      move: (size _) h_1 h_2 => *; split; apply /ZleP; lia.
    by rewrite wsize8; lia.   
  have [s3 [hssem hvalid3]] := check_cP (P:= P) SP.(p_funcs) Hstk Hglob hdisj H3 hc hvalid2.
  have [vres1 [H1' uincl1]]:= check_varsP hres (valid_vm hvalid3) H4.
  have [vres2 htr uincl2]:= mapM2_truncate_val H5 uincl1.
  exists (free_stack (emem s3) stk_size), vres2.
  split => //; split.
  + have /Memory.free_stackP [h1 h2 h3 h4 (* h5 *)]: 
     omap snd (ohead (frames(emem s3))) = Some stk_size.
    + by rewrite (valid_top_frame hvalid3).
    have [u1 u2 u3 u4 u5] := hm2.
    have vdisj: forall w sz, validw m1' w sz ->  disjoint_zrange (top_stack m2s) stk_size w (wsize_size sz).
    + subst m1'; move=> w sz hw; have [ /negP /andP] := valid_disj hvalid3 hw.
      rewrite {1 2}/is_true !Z.ltb_lt => ??; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow; apply (Memory.valid_align hw).
      lia.
    subst m1';split => //.
    + move=> w sz hw.
      rewrite (valid_eq hvalid3) // h1 // h2 (valid_def hvalid3) /= hw /=; split=> //.
      by rewrite (valid_top hvalid3); apply vdisj.
    + by move=> w sz /(valid_disj hvalid3) [].
    + move=> w sz. 
      apply Bool.eq_iff_eq_true; have := h2 w sz.
      rewrite {1}/is_true => ->.
      rewrite (valid_def hvalid3) /= (valid_top hvalid3); split.
      + move=> [] /orP [].
        + move=> /orP [-> //| ].
          move=> /andP [] /andP [] /ZleP ? /ZleP ?? [???].
          by have := wsize_size_pos sz;lia.
        by move=> /andP [-> ->] /=;rewrite orbT.         
      move=> /orP [ hw | /andP [hb hal]]. 
      + by rewrite hw /=;split => //; apply: vdisj.
      rewrite hb hal !orbT;split => //; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow.
      have : validw m2 w sz by rewrite u4 hb hal /= orbT.
      have [_ _ _ _ h _]:= Memory.alloc_stackP ha.
      by move=> /h; lia.
    move=> i [hi1 hi2].
    rewrite -h1.
    + by rewrite (valid_glob hvalid3).
    rewrite h2 (valid_top hvalid3) (valid_def hvalid3) is_align8 !andbT; split.
    + apply /orP;right; apply /andP.
      rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP.
      lia. move: hi1 hi2; rewrite /h4; move: (size _) => *;lia.
    split.
    + by apply /ZleP; case: Hstk.
    + by apply is_align_no_overflow; apply is_align8.
    have :  validw m2 (rip + wrepr U64 i) U8.
    + rewrite u4 is_align8 andbT; apply /orP;right.
      by apply /andP; rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP;lia.
    have [_ _ _ _ h _]:= Memory.alloc_stackP ha.
    by move=> /h;lia.
  econstructor;eauto.
  move: hap hssem => /=; rewrite /alloc_prog.
  by case: oracle_g => -[???]; t_xrbindP => ??; case:ifP => // ?; t_xrbindP => ?? <-.
Qed.


(* R et Rout: liens entre les valeurs avant et après stack_alloc.
   R ty_in va va': va' = va si None et reg ptr (pointe vers une zone dans laquelle il y a va)
   et si reg ptr est writable, il doit être disjoint de tous les autres trucs
   et dans la pile

   Rout peut-être qu'on a besoin de prendre va' en argument pour dire que vr' = va'
   (en tout cas même région) dans le cas reg ptr

   mais on a plus accès à reg ptr ou pas (sao.(sao_params)), en tout cas, il me semble
   peut-être utiliser le ty_in de fn dans P et SP :
   - si =, va = va',
   - si <>, va' = Vword p...
*)
Lemma alloc_progP nrip data oracle_g oracle (P: uprog) (SP: sprog) fn:
  alloc_prog nrip data oracle_g oracle P = ok SP ->
  forall ev m1 va va' m1' vr rip, 
    sem_call (sCP := sCP_unit) P ev m1 fn va m1' vr ->
    R (get_fundef fn).(f_tyin) va va' ->
    forall m2, extend_mem m1 m2 rip SP.(p_extra).(sp_globs) ->
    alloc_ok SP fn m2 ->
    exists m2' vr',
      Rout (get_fundef fn).(f_tyout) va' vr vr' /\
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(p_extra).(sp_globs) /\
      sem_call (sCP := sCP_stack) SP rip m2 fn va m2' vr'.
      (* /\ mem_unchanged' fn m1 m1' m2' vargs'. ?? *)
Proof.
  move=> Hcheck ev m1 va m1' vr rip hsem m2 he ha.
  have [fd hget]: exists fd, get_fundef (p_funcs P) fn = Some fd.
  + by case: hsem=> ??? fd *;exists fd.
  have := check_cP.
  move=> /(_ P ev rip _ _ _ _ _ _ _ SP _ oracle _ _ _ _ _ _ hsem _ he ha).
  apply.
  
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc Hcheck.
  have [fd' [hgetS ?]]:= hf _ _ hget.
  by apply: (alloc_fdP Hcheck hget hgetS hsem he (ha _ hgetS)).
Qed.
