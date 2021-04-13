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
Require Export psem stack_alloc.
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

(* --------------------------------------------------------------------------- *)

Section Section.

Variables (pmap:pos_map) (stk_size glob_size:Z).
Variables (rsp rip: ptr).

(* TODO: v_scope -> Sv.t ? *)
Variable (Slots : Sv.t).
Variable (Addr : slot -> ptr).
Variable (Writable : slot -> bool).
Variable (Align : slot -> wsize).

(* Any pointer in a slot is valid. *)
Definition slot_valid m := forall s p, Sv.In s Slots ->
  between (Addr s) (size_slot s) p U8 -> validw m p U8.

(* NOTE: disjoint_zrange already contains no_overflow conditions *)
(* Slots are disjoint from the source memory [ms]. *)
Definition disjoint_source ms :=
  forall s p, Sv.In s Slots -> validw ms p U8 ->
  disjoint_zrange (Addr s) (size_slot s) p (wsize_size U8).

(* Addresses of slots can be manipulated without risking overflows. *)
Hypothesis addr_no_overflow : forall s, Sv.In s Slots ->
  no_overflow (Addr s) (size_slot s).

(* Two distinct slots, with at least one of them writable, are disjoint. *)
Hypothesis disjoint_writable : forall s1 s2,
  Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
  Writable s1 ->
  disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2).

(* The address [Addr s] of a slot s is aligned w.r.t. [Align s]. *)
Hypothesis slot_align :
  forall s, Sv.In s Slots -> is_align (Addr s) (Align s).

(* All pointers valid in memory [m0] are valid in memory [m].
   It is supposed to be applied with [m0] the initial target memory
   and [m] the current target memory.
*)
Definition valid_incl m0 m :=
  forall p, validw m0 p U8 -> validw m p U8.

(* ms: source memory
   m0: initial target memory
   m: current target memory

   ms:
                                              --------------------
                                              |    mem source    |
                                              --------------------

   m0:
                 --------------- ------------ --------------------
                 | other stack | |   glob   | |    mem source    |
                 --------------- ------------ --------------------

                                  ||
                                  || function call
                                  \/

   m:
   ------------- --------------- ------------ --------------------
   |   stack   | | other stack | |   glob   | |    mem source    |
   ------------- --------------- ------------ --------------------

*)

(* The memory zones that are not in a writable slot remain unchanged. *)
Definition mem_unchanged ms m0 m :=
  forall p, validw m0 p U8 -> ~ validw ms p U8 ->
  (forall s, Sv.In s Slots -> Writable s -> disjoint_zrange (Addr s) (size_slot s) p (wsize_size U8)) ->
  read m0 p U8 = read m p U8.

(* The stack and the global space are disjoint (if both non-trivial) *)
(* TODO: Is this really needed? *)
Hypothesis disj_rsp_rip :
  0 < stk_size -> 0 < glob_size ->
  wunsigned rsp + stk_size <= wunsigned rip \/ wunsigned rip + glob_size <= wunsigned rsp.

(* TODO: move ? *)
Lemma valid_align m p ws :
  validw m p ws →
  is_align p ws.
Proof. by case/validwP. Qed.

Hint Resolve is_align_no_overflow valid_align.

Record wf_global g ofs ws := {
  wfg_slot : Sv.In g Slots;
  wfg_writable : ~ Writable g;
  wfg_align : Align g = ws;
  wfg_offset : Addr g = (rip + wrepr Uptr ofs)%R
}.

Definition wbase_ptr sc :=
  if sc == Sglob then rip else rsp.

Record wf_direct (x : var) (s : slot) ofs ws z sc := {
  wfd_slot : Sv.In s Slots;
  wfd_size : size_slot x <= z.(z_len);
  wfd_zone : 0 <= z.(z_ofs) /\ z.(z_ofs) + z.(z_len) <= size_slot s;
  wfd_writable : Writable s = (sc != Sglob);
  wfd_align : Align s = ws;
  wfd_offset : Addr s = (wbase_ptr sc + wrepr Uptr ofs)%R
}.

(* TODO : move elsewhere *)
(* but not clear where
   Uptr is defined in memory_model, no stype there
   stype is defined in type, no Uptr there
*)
Notation sptr := (sword Uptr) (only parsing).

Record wf_regptr x xr := {
  wfr_type : is_sarr (vtype x);
  wfr_rtype : vtype xr = sptr;
  wfr_not_vrip : xr <> pmap.(vrip);
  wfr_not_vrsp : xr <> pmap.(vrsp);
  wfr_new : Sv.In xr pmap.(vnew);
  wfr_distinct : forall y yr,
    get_local pmap y = Some (Pregptr yr) -> x <> y -> xr <> yr
}.

Record wf_stkptr (x : var) (s : slot) ofs ws z (xf : var) := {
  wfs_slot : Sv.In s Slots;
  wfs_type : is_sarr (vtype x);
  wfs_size : wsize_size Uptr <= z.(z_len);
  wfs_zone : 0 <= z.(z_ofs) /\ z.(z_ofs) + z.(z_len) <= size_slot s;
  wfs_writable : Writable s;
  wfs_align : Align s = ws;
  wfs_align_ptr : (Uptr <= ws)%CMP;
  wfs_offset_align : is_align (wrepr _ z.(z_ofs))%R Uptr;
  wfs_offset : Addr s = (rsp + wrepr Uptr ofs)%R;
(*   wfs_ftype : vtype xf = sptr; *)
  wfs_new : Sv.In xf pmap.(vnew);
  wfs_distinct : forall y s' ofs' ws' z' yf,
    get_local pmap y = Some (Pstkptr s' ofs' ws' z' yf) -> x <> y -> xf <> yf
}.

(* ou faire un match *)
Definition wf_local x pk :=
  match pk with
  | Pdirect s ofs ws z sc => wf_direct x s ofs ws z sc
  | Pregptr xr => wf_regptr x xr
  | Pstkptr s ofs ws z xf => wf_stkptr x s ofs ws z xf
  end.

Class wf_pmap := {
  wt_rip     : vtype pmap.(vrip) = sword Uptr;
  wt_rsp     : vtype pmap.(vrsp) = sword Uptr;
  rip_in_new : Sv.In pmap.(vrip) pmap.(vnew);
  rsp_in_new : Sv.In pmap.(vrsp) pmap.(vnew);
  wf_globals : forall g ofs ws, Mvar.get pmap.(globals) g = Some (ofs, ws) -> wf_global g ofs ws;
  wf_locals  : forall x pk, Mvar.get pmap.(locals) x = Some pk -> wf_local x pk;
  wf_vnew    : forall x pk, Mvar.get pmap.(locals) x = Some pk -> ~ Sv.In x pmap.(vnew)
}.

(* Declare Instance wf_pmapI : wf_pmap. *)

(* Well-formedness of a [region]. *)
Record wf_region (r : region) := {
  wfr_slot     : Sv.In r.(r_slot) Slots;
  wfr_writable : Writable r.(r_slot) = r.(r_writable);
  wfr_align    : Align r.(r_slot) = r.(r_align);
}.

(* Well-formedness of a [zone]. *)
Record wf_zone (z : zone) (ty : stype) (sl : slot) := {
  wfz_len : size_of ty <= z.(z_len);
    (* the zone is big enough to store a value of type [ty] *)
  wfz_ofs : 0 <= z.(z_ofs) /\ z.(z_ofs) + z.(z_len) <= size_slot sl
    (* the zone is a small enough to be in slot [sl] *)
}.

(* Well-formedness of a [sub_region]. *)
Record wf_sub_region (sr : sub_region) ty := {
  wfsr_region :> wf_region sr.(sr_region);
  wfsr_zone   :> wf_zone sr.(sr_zone) ty sr.(sr_region).(r_slot)
}.

(* TODO: Tout exprimer à partier de check_gvalid ? *)
Definition wfr_WF (rmap : region_map) :=
  forall x sr,
    Mvar.get rmap.(var_region) x = Some sr ->
    wf_sub_region sr x.(vtype).

(* TODO :
  - invariant : si une variable n'est pas un tableau, alors sa région a exactement sa taille (peut-être pas nécessaire)
  - gros invariant restant : parler des bytes valides !
  - invariant : si je suis dans local_map, je ne suis ni int ni bool
  - dire des trucs sur la map region_var
*)

(*Definition valid_mp mp ty := 
  exists x, 
    subtype ty (vtype x) /\
    if mp.(mp_s) == MSglob then get_global pmap x = ok mp.(mp_ofs)
    else get_local pmap x = Some (Pstack mp.(mp_ofs)).
*)

(* Registers (not introduced by the compiler) hold the same value in [vm1] and [vm2] *)
Definition eq_vm (vm1 vm2:vmap) := 
  forall (x:var),
    Mvar.get pmap.(locals) x = None ->
    ~ Sv.In x pmap.(vnew) ->
    get_var vm1 x = get_var vm2 x.

(*
Definition wptr ms := 
  if ms == MSglob then rip else rsp.

Definition wptr_size sc :=
  if sc == Sglob then glob_size else stk_size.

Definition disjoint_ptr m :=
  forall w sz ms,
    validw m w sz ->
    ~ ( wunsigned (wbase_ptr ms) < wunsigned w + wsize_size sz /\ wunsigned w < wunsigned (wbase_ptr ms) + wptr_size ms).
*)
Definition sub_region_addr sr :=
  (Addr sr.(sr_region).(r_slot) + wrepr _ sr.(sr_zone).(z_ofs))%R.
(* 
(* TODO : could we merge [eq_mp_word] and [eq_mp_array] ? *)
Definition eq_sub_region_word (m2:mem) sr bytes sz v := 
  exists w:word sz,
    v = Vword w /\
    (ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) (Some 0) (wsize_size sz))) ->
      read_mem m2 (sub_region_addr sr) sz = ok w).

Definition eq_sub_region_array (m2:mem) sr bytes s v := 
  exists (a:WArray.array s),
   v = Varr a /\
   forall off, (0 <= off < Zpos s)%Z ->
     ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + off) ->
     forall v, WArray.get AAscale U8 a off = ok v ->
     read_mem m2 (sub_region_addr sr + wrepr _ off) U8 = ok v. *)

(* Definition get_val_byte v off :=
  match v with
  | Vword ws w => 
    let a := WArray.empty (Z.to_pos (wsize_size ws)) in
    Let a := WArray.set a AAscale 0 w in
    WArray.get AAscale U8 a off
  | Varr _ a => WArray.get AAscale U8 a off
  | _ => type_error
  end. *)

(* Size of a value. *)
Notation size_val v := (size_of (type_of_val v)).

(* TODO: should we raise another error in the Vword case ? *)
(* This allows to read uniformly in words and arrays. *)
Definition get_val_byte v off :=
  match v with
  | Vword ws w => if ((0 <=? off) && (off <? wsize_size ws)) then ok (LE.wread8 w off) else type_error
  | Varr _ a => read a off U8
  |_ => type_error
  end.

(*
Definition get_val_byte v off :=
  match v with
  | Vword ws w => if ((0 <= off) && (off < wsize_size ws))%CMP then ok (nth 0%R (LE.encode w) (Z.to_nat off)) else type_error
  | Varr _ a => WArray.get AAscale U8 a off
  | _ => type_error
  end.
*)

Definition eq_sub_region_val_read (m2:mem) sr bytes v :=
  forall off,
     ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + off) ->
     forall w, get_val_byte v off = ok w ->
     read m2 (sub_region_addr sr + wrepr _ off)%R U8 = ok w.

Definition eq_sub_region_val ty m2 sr bytes v :=
  eq_sub_region_val_read m2 sr bytes v /\
  (* According to the psem semantics, a variable of type [sword ws] can store
     a value of type [sword ws'] of shorter size (ws' <= ws).
     But actually, this is used only for register variables.
     For stack variables, we check in [alloc_lval] in stack_alloc.v that the
     value has the same size as the variable, and we remember that fact here.
  *)
  (* Actually, it is handful to know that [ty] and [type_of_val v] are the same
     even in the non-word cases.
  *)
  type_of_val v = ty.

(*
Definition eq_sub_region_val ty (m2:mem) sr bytes v := 
  match ty with
  | sword ws => eq_sub_region_word m2 sr bytes ws v
  | sarr  s  => eq_sub_region_array m2 sr bytes s v 
  | _        => True
  end.*)

Variable (P: uprog) (ev: extra_val_t (progT := progUnit)).
Notation gd := (p_globs P).

(* FIXME : est-ce qu'on teste la bonne zone dans le cas skptr ?
   Doit-on tester une largeur de z_len ou plus précisément Uptr ?
*)
Definition valid_pk rmap (s2:estate) sr pk :=
  match pk with
  | Pdirect s ofs ws z sc =>
    sr = sub_region_direct s ws sc z
  | Pstkptr s ofs ws z f => (*
    let srf := sub_region_stkptr s ws z in
    let bytes := get_var_bytes rmap srf.(sr_region) f in
    let i := interval_of_zone (sub_zone_at_ofs z (Some 0) (wsize_size Uptr)) in
    ByteSet.mem bytes i -> *)
    check_stack_ptr rmap s ws z f ->
    read s2.(emem) (sub_region_addr (sub_region_stkptr s ws z)) Uptr = ok (sub_region_addr sr)
    (* si f est dans la rmap et que ses bytes sont sets, 
    exists sr', Mvar.get f rmap.(var_region) = Some sr' /\
    read_mem s2.(emem) (sub_region_addr sr') Uptr = ok (sub_region_addr sr) *)
    (* read_mem s2.(emem) (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) Uptr = ok (mp_addr mp) *)
  | Pregptr p =>
    get_var s2.(evm) p = ok (Vword (sub_region_addr sr))
  end.

(* TODO: could we have this in stack_alloc.v ?
   -> could be used in check_valid/set_arr_word...
   This could mean useless checks for globals, but maybe worth it
   cf. check_vpk_word ?
   Not clear : one advantage of using vpk is to avoid two calls to
   pmap.(globals) and pmap.(locals)
   Could pmap.(globlals) and pmap.(locals) directly return sub_regions ?
*)
Definition check_gvalid rmap x : option (sub_region * ByteSet.t) :=
  if is_glob x then 
    omap (fun '(_, ws) =>
      let sr := sub_region_glob x.(gv) ws in
      let bytes := ByteSet.full (interval_of_zone sr.(sr_zone)) in
      (sr, bytes)) (Mvar.get pmap.(globals) (gv x))
  else
    let sr := Mvar.get rmap.(var_region) x.(gv) in
    match sr with
    | Some sr =>
      let bytes := get_var_bytes rmap.(region_var) sr.(sr_region) x.(gv) in
      Some (sr, bytes)
    | _ => None
    end.

(* wfr_get_v_mp : 
    forall x xs mp, Mmp.get rmap.(region_vars) mp = Some xs ->
                    Sv.In x xs -> Mvar.get rmap.(var_region) x = Some mp;*)
(*
Definition wfr_VALID (rmap:regions) :=
   forall x mp, Mvar.get rmap.(var_region) x = Some mp -> valid_mp mp (vtype x).
*)
Definition wfr_VAL (rmap:region_map) (s1:estate) (s2:estate) :=
  forall x sr bytes v, check_gvalid rmap x = Some (sr, bytes) -> 
    get_gvar gd s1.(evm) x = ok v ->
    eq_sub_region_val x.(gv).(vtype) s2.(emem) sr bytes v.

Definition wfr_PTR (rmap:region_map) (s2:estate) :=
  forall x sr, Mvar.get (var_region rmap) x = Some sr ->
    exists pk, get_local pmap x = Some pk /\ valid_pk rmap s2 sr pk.

Class wf_rmap (rmap:region_map) (s1:estate) (s2:estate) := {  
(*   wfr_valid_mp :  wfr_VALID rmap; *)
  wfr_wf  : wfr_WF rmap;
  wfr_val : wfr_VAL rmap s1 s2;
  wfr_ptr : wfr_PTR rmap s2;
}.

Definition eq_mem_source (m1 m2:mem) := 
  forall w, validw m1 w U8 -> read m1 w U8 = read m2 w U8.
(*
Definition eq_not_mod (m0 m2:mem) := 
  forall ofs, 
     0 <= ofs < stk_size ->
     (forall x xofs xty, 
        local_pos x = Some(xofs, xty) -> 
        xofs + size_of xty <= ofs \/ ofs + 1 <= xofs) ->
     read_mem m0 (rsp + (wrepr _ ofs)) U8 = 
     read_mem m2 (rsp + (wrepr _ ofs)) U8.

Class valid_state (rmap:regions) (m0:mem) (s1:estate) (s2:estate) := {
   vs_val_ptr : 
      forall s w, (0 <= wunsigned w < wptr_size s) -> valid_pointer (emem s2) (wptr s + w) U8;
   vs_disj      : disjoint_ptr (emem s1);
   vs_top_frame : ohead (frames (emem s2)) = Some (rsp, stk_size);
   vs_eq_vm     : eq_vm s1.(evm) s2.(evm);
   vs_wf_region :> wf_region rmap s1 s2;
   vs_eq_mem    : eq_glob s1.(emem) s2.(emem);
   vs_eq_not_mod: eq_not_mod m0 s2.(emem);
}.
*)

Hypothesis wf_pmap0 : wf_pmap.

(* FIXME: could we put [ms] as section variable ? it should not be modified? *)
(* TODO: add comments *)
Class valid_state (rmap : region_map) (m0 : mem) (s1 s2 : estate) := {
  vs_slot_valid : slot_valid s2.(emem);
  vs_disjoint   : disjoint_source s1.(emem);
  vs_valid_incl : valid_incl s1.(emem) s2.(emem); (* is it correct? *)
  vs_unchanged  : mem_unchanged s1.(emem) m0 s2.(emem); (* is it correct? *)
  vs_rip        : get_var (evm s2) pmap.(vrip) = ok (Vword rip);
  vs_rsp        : get_var (evm s2) pmap.(vrsp) = ok (Vword rsp);
  vs_eq_vm      : eq_vm s1.(evm) s2.(evm);
  vs_wf_region  :> wf_rmap rmap s1 s2;
  vs_eq_mem     : eq_mem_source s1.(emem) s2.(emem)
}.

(* [valid_state]'s clauses deal about U8 only. We show that they imply
   their counterpart with any [ws].
*)

(* why [w] is implicit by default?? *)
Lemma ge0_wunsigned ws (w:word ws) : 0 <= wunsigned w.
Proof. by case (wunsigned_range w). Qed.
Global Arguments ge0_wunsigned [_] _.

(* Question : how this proof works in the case of sword ??? *)
(* TODO: cleanup, we have size_of_pos size_of_gt0 size_slot_gt0 ! *)
Lemma size_of_gt0 ty : 0 < size_of ty.
Proof. by case: ty. Qed.

Lemma disjoint_zrange_add p sz p' sz1 sz2 :
  0 < sz ->
  0 <= sz1 ->
  0 < sz2 ->
  no_overflow p' (sz1 + sz2) ->
  disjoint_zrange p sz p' sz1 ->
  disjoint_zrange p sz (p' + wrepr _ sz1) sz2 ->
  disjoint_zrange p sz p' (sz1 + sz2).
Proof.
  move=> hsz hsz1 hsz2.
  rewrite /no_overflow zify => ho.
  case; rewrite /no_overflow !zify => ho11 ho12 hd1.
  case; rewrite /no_overflow !zify.
  rewrite wunsigned_add; last by have := ge0_wunsigned p'; lia.
  move => ho21 ho22 hd2.
  split; rewrite /no_overflow ?zify; lia.
Qed.

(* TODO: or disjoint_zrange_byte_something ? *)
Lemma disjoint_zrange_U8 p sz p' sz' :
  0 < sz ->
  0 < sz' ->
  no_overflow p' sz' ->
  (forall k, 0 <= k /\ k < sz' -> disjoint_zrange p sz (p' + wrepr _ k) (wsize_size U8)) ->
  disjoint_zrange p sz p' sz'.
Proof.
  move=> hsz /dup[] /Z.lt_le_incl.
  move: sz'.
  apply: natlike_ind.
  - lia.
  - move=> sz' hsz' IH _ hover hd.
    have /Z_le_lt_eq_dec [?|?] := hsz'.
    + apply disjoint_zrange_add => //.
      + apply IH => //.
        + by move: hover; rewrite /no_overflow !zify; lia.
        by move=> k hk; apply hd; lia.
      by apply hd; lia.
    subst sz'.
    have := hd 0 ltac:(done).
    rewrite wrepr0 GRing.addr0.
    by apply.
Qed.

Lemma disjoint_source_word rmap m0 s1 s2 :
  valid_state rmap m0 s1 s2 ->
  forall s p ws,
    Sv.In s Slots -> validw s1.(emem) p ws ->
    disjoint_zrange (Addr s) (size_slot s) p (wsize_size ws).
Proof.
  move=> hvs s p ws hin /validwP [] /is_align_no_overflow hover hd.
  apply disjoint_zrange_U8 => //.
  + apply size_of_gt0.
  by move=> k hk; apply vs_disjoint => //; apply hd.
Qed.

Lemma valid_incl_word rmap m0 s1 s2 p ws :
  valid_state rmap m0 s1 s2 ->
  validw s1.(emem) p ws ->
  validw s2.(emem) p ws.
Proof.
  move=> hvs /validwP [hal hvalid].
  apply /validwP; split=> //.
  move=> k hk; apply vs_valid_incl.
  by apply hvalid.
Qed.

Lemma eq_mem_source_word rmap m0 s1 s2 p ws :
  valid_state rmap m0 s1 s2 ->
  validw s1.(emem) p ws ->
  read s1.(emem) p ws = read s2.(emem) p ws.
Proof.
  move=> hvs /validwP [hal hvalid].
  apply eq_read.
  by move=> k hk; apply vs_eq_mem; apply hvalid.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma get_globalP x z : get_global pmap x = ok z <-> Mvar.get pmap.(globals) x = Some z.
Proof.
  rewrite /get_global; case: Mvar.get; last by split.
  by move=> ?;split => -[->].
Qed.

Lemma get_gvar_glob gd x vm : is_glob x -> get_gvar gd vm x = sem.get_global gd (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob => /eqP ->. Qed.

Lemma get_gvar_nglob gd x vm : ~~is_glob x -> get_gvar gd vm x = get_var vm (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob; case: (gs x). Qed.

Lemma cast_ptrP gd s e i : sem_pexpr gd s e >>= to_int = ok i ->
  sem_pexpr gd s (cast_ptr e) = ok (Vword (wrepr U64 i)).
Proof. by t_xrbindP => v he hi ;rewrite /cast_ptr /cast_w /= he /sem_sop1 /= hi. Qed.

Lemma cast_wordP gd s e i : 
  sem_pexpr gd s e >>= to_int = ok i ->
  exists sz (w:word sz), sem_pexpr gd s (cast_word e) = ok (Vword w) /\
                         truncate_word U64 w = ok (wrepr U64 i).
Proof.
  move=> he.
  have : exists sz (w:word sz), 
              sem_pexpr gd s (cast_ptr e) = ok (Vword w) /\
                      truncate_word U64 w = ok (wrepr U64 i). 
  + exists U64, (wrepr U64 i); split; first by apply cast_ptrP.
    by rewrite truncate_word_u.
  case: e he => // -[] // [] //=.
  move=> e he _; move: he; rewrite /sem_sop1 /=; t_xrbindP => v v' -> w.
  move=> /to_wordI [sw [w' [hsw -> ->]]] <- [<-].
  by exists sw, w'; split => //; rewrite /truncate_word hsw wrepr_unsigned.
Qed.

(* TODO: gd or [::] ? *)
Lemma mk_ofsP aa sz gd s2 ofs e i :
  sem_pexpr gd s2 e >>= to_int = ok i ->
  sem_pexpr gd s2 (mk_ofs aa sz e ofs) = ok (Vword (wrepr U64 (i * mk_scale aa sz + ofs)%Z)).
Proof.
  rewrite /mk_ofs; case is_constP => /= [? [->] //| {e} e he] /=.
  rewrite /sem_sop2 /=.
  have [sz' [w [-> /= -> /=]]]:= cast_wordP he.
  by rewrite !zero_extend_u wrepr_add wrepr_mul GRing.mulrC. 
Qed.

(*
Lemma check_validP rmap x ofs len mps : 
  check_valid rmap x ofs len = ok mps <->
  (Mvar.get (var_region rmap) x = Some mps /\
   exists xs, Mmp.get (region_var rmap) mps.(mps_mp) = Some xs /\ Sv.In x xs).
Proof.
  rewrite /check_valid.
  case heq: Mvar.get => [mp' |]; last by intuition.
  case heq1 : Mmp.get => [xs | /=]; last by split => // -[] [?]; subst mp'; rewrite heq1 => -[] ?[].
  case: ifPn => /Sv_memP hin /=.
  + split => [ [?] | [[?] ]]; subst mp' => //.
    by split => //;exists xs.
  by split => // -[] [?]; subst mp'; rewrite heq1 => -[xs'] [[<-]] /hin.
Qed.
*)

(* TODO: gd or [::] ? *)
(* TODO: version where mk_ofsi = ok -> *)
Lemma mk_ofsiP gd s e i aa sz :
  Let x := sem_pexpr gd s e in to_int x = ok i ->
  mk_ofsi aa sz e <> None ->
  mk_ofsi aa sz e = Some (i * mk_scale aa sz).
Proof. by case: e => //= _ [->]. Qed.

Section EXPR.
  Variables (rmap:region_map) (m0:mem) (s:estate) (s':estate).
  Hypothesis (hvalid: valid_state rmap m0 s s').

  (* If [x] is a register : it is not impacted by the presence of global
     variables per hypothesis [vs_eq_vm]
  *)
  Lemma get_var_kindP x v:
    get_var_kind pmap x = ok None ->
    ~ Sv.In x.(gv) pmap.(vnew) ->
    get_gvar gd (evm s) x = ok v ->
    get_gvar [::] (evm s') x = ok v.
  Proof.
    rewrite /get_var_kind; case: ifPn => hglob; first by t_xrbindP.
    case hgl : get_local => // _ /(vs_eq_vm hgl) heq.
    by rewrite !get_gvar_nglob // heq.
  Qed.

  Lemma base_ptrP sc : get_var (evm s') (base_ptr pmap sc) = ok (Vword (wbase_ptr sc)).
  Proof. by case: sc => /=; [apply: vs_rsp | apply: vs_rip]. Qed.

  (* TODO : move => in fact already exists in memory_example *)
  Lemma wsize_le_div ws1 ws2 : (ws1 <= ws2)%CMP -> (wsize_size ws1 | wsize_size ws2).
  Proof.
(*     apply memory_example.wsize_size_le. *)
    by case: ws1; case: ws2 => //= _; apply: Znumtheory.Zmod_divide.
  Qed.

  (* TODO : shorter and more elegant proof? *)
  Lemma Zland_mod z ws : Z.land z (wsize_size ws - 1) = 0 -> z mod wsize_size ws = 0.
  Proof.
    by case: ws => /=;
      set len := (wsize_size _);
      change len with (2 ^ (Z.log2 len));
      rewrite -Z.land_ones.
  Qed.

  Lemma wunsigned_repr_le ws z : 0 <= z -> wunsigned (wrepr ws z) <= z. 
  Proof. by move=> hz; rewrite wunsigned_repr; apply Z.mod_le. Qed.

  Lemma size_slot_gt0 sl : 0 < size_slot sl.
  Proof. by apply size_of_gt0. Qed.

  Lemma wf_zone_len_gt0 z ty sl : wf_zone z ty sl -> 0 < z.(z_len).
  Proof. by move=> [? _]; have := size_of_gt0 ty; lia. Qed.

  (* probably subsumed by slot_wunsigned_addr. TODO: remove *)
  Lemma slot_wrepr sr ty : wf_sub_region sr ty ->
    wunsigned (wrepr U64 sr.(sr_zone).(z_ofs)) = sr.(sr_zone).(z_ofs).
  Proof.
    move=> hwf; rewrite wunsigned_repr -/(wbase Uptr).
    have hlen := wf_zone_len_gt0 hwf.
    have hofs := wfz_ofs hwf.
    have /ZleP hno := addr_no_overflow (wfr_slot hwf).
    have ? := ge0_wunsigned (Addr sr.(sr_region).(r_slot)).
    by apply Zmod_small; lia.
  Qed.

  Lemma wunsigned_sub_region_addr sr ty : wf_sub_region sr ty ->
    wunsigned (sub_region_addr sr) = wunsigned (Addr sr.(sr_region).(r_slot)) + sr.(sr_zone).(z_ofs).
  Proof.
    move=> hwf; apply wunsigned_add.
    have hlen := wf_zone_len_gt0 hwf.
    have hofs := wfz_ofs hwf.
    have /ZleP hno := addr_no_overflow (wfr_slot hwf).
    have ? := ge0_wunsigned (Addr (sr.(sr_region).(r_slot))).
    by lia.
  Qed.

(* TODO
  Lemma check_validP x ofs len mps :
    check_valid rmap x.(gv) ofs len = ok (mps) ->
*)
  Lemma check_alignP sr ty ws tt :
    wf_sub_region sr ty ->
    check_align sr ws = ok tt ->
    is_align (sub_region_addr sr) ws.
  Proof.
    move=> hwf; rewrite /check_align; t_xrbindP => ? /assertP halign /assertP /eqP halign2.
    rewrite /sub_region_addr; apply: is_align_add.
    + apply: (is_align_m halign); rewrite -(wfr_align hwf).
      by apply: slot_align; apply: (wfr_slot hwf).
    by apply /is_align_mod; apply Zland_mod; rewrite (slot_wrepr hwf).
  Qed.
(*
  Lemma region_glob_wf x ofs_align :
    Mvar.get (globals pmap) x = Some ofs_align ->
    wf_region (region_glob x ofs_align).
  Proof.
    case: ofs_align=> ofs ws.
    by move=> /wf_globals [*]; rewrite /region_glob; split=> //=; apply /idP.
  Qed.
*)
  Lemma sub_region_glob_wf x ofs ws :
    wf_global x ofs ws ->
    wf_sub_region (sub_region_glob x ws) x.(vtype).
  Proof.
    move=> [*]; split.
    + by split=> //; apply /idP.
    by split=> /=; lia.
  Qed.

  Lemma get_sub_regionP x sr :
    get_sub_region rmap x = ok sr <-> Mvar.get rmap.(var_region) x = Some sr.
  Proof.
    rewrite /get_sub_region; case: Mvar.get; last by split.
    by move=> ?; split => -[->].
  Qed.

  (* TODO: should probably become size_at_ofs : Z *)
  Definition stype_at_ofs (ofs : option Z) (ty ty' : stype) :=
    if ofs is None then ty' else ty.

  (* Sans doute à généraliser pour n'importe quelle longueur *)
  (* wsize_size ws -> len *)
  Lemma sub_region_at_ofs_wf sr ty (* ws *) ofs ty2 (* len *) :
    wf_sub_region sr ty ->
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty2 <= size_of ty) ->
    wf_sub_region (sub_region_at_ofs sr ofs (size_of ty2)) (stype_at_ofs ofs ty2 ty).
  Proof.
    move=> hwf hofs /=; split; first by apply hwf.(wfsr_region).
    case: ofs hofs => [ofs|_] /=; last by apply hwf.
    move=> /(_ _ refl_equal) ?.
    split=> /=; first by auto with zarith.
    have hlen := hwf.(wfz_len).
    have hofs := hwf.(wfz_ofs).
    by lia.
 Qed.

  Lemma zbetween_sub_region_addr sr ty : wf_sub_region sr ty ->
    zbetween (Addr sr.(sr_region).(r_slot)) (size_slot sr.(sr_region).(r_slot))
      (sub_region_addr sr) (size_of ty).
  Proof.
    move=> hwf; rewrite /zbetween !zify (wunsigned_sub_region_addr hwf).
    have hofs := hwf.(wfz_ofs).
    have hlen := hwf.(wfz_len).
    by lia.
  Qed.

  (* TODO: move (and rename?) *)
  Lemma mem_full i : ByteSet.mem (ByteSet.full i) i.
  Proof. by apply /ByteSet.memP => k; rewrite ByteSet.fullE. Qed.

  Definition zbetween_zone z1 z2 :=
    (z1.(z_ofs) <=? z2.(z_ofs)) && (z2.(z_ofs) + z2.(z_len) <=? z1.(z_ofs) + z1.(z_len)).

  Lemma zbetween_zone_refl z : zbetween_zone z z.
  Proof. by rewrite /zbetween_zone !zify; lia. Qed.

  Lemma zbetween_zone_trans z1 z2 z3 :
    zbetween_zone z1 z2 ->
    zbetween_zone z2 z3 ->
    zbetween_zone z1 z3.
  Proof. by rewrite /zbetween_zone !zify; lia. Qed.

  (* FIXME: why are we using CMP on Z ?? *)
  (* TODO : put that lemma in zify ? *)
  Lemma Zcmp_le i1 i2 : (i1 <= i2)%CMP = (i1 <=? i2)%Z.
  Proof.
    rewrite /cmp_le /gcmp /Mz.K.cmp /Z.leb -Zcompare_antisym.
    by case: Z.compare.
  Qed.

  Lemma disjoint_zones_incl z1 z1' z2 z2' :
    zbetween_zone z1 z1' ->
    zbetween_zone z2 z2' ->
    disjoint_zones z1 z2 ->
    disjoint_zones z1' z2'.
  Proof. by rewrite /zbetween_zone /disjoint_zones !Zcmp_le !zify; lia. Qed.

  Lemma disjoint_zones_incl_l z1 z1' z2 :
    zbetween_zone z1 z1' ->
    disjoint_zones z1 z2 ->
    disjoint_zones z1' z2.
  Proof. by move=> ?; apply disjoint_zones_incl => //; apply zbetween_zone_refl. Qed.

  Lemma disjoint_zones_incl_r z1 z2 z2' :
    zbetween_zone z2 z2' ->
    disjoint_zones z1 z2 ->
    disjoint_zones z1 z2'.
  Proof. by move=> ?; apply disjoint_zones_incl => //; apply zbetween_zone_refl. Qed.

  Lemma subset_interval_of_zone z1 z2 :
    I.subset (interval_of_zone z1) (interval_of_zone z2) = zbetween_zone z2 z1.
  Proof.
    rewrite /I.subset /interval_of_zone /zbetween_zone /=.
    by apply /idP/idP; rewrite !zify; lia.
  Qed.

  (* The assumption on [ofs] is different from other lemmas (where we use
     [size_slot x] instead of [z.(z_len)] as upper bound), since we do not
     have a slot at hand. Is it a problem?
     -> this was changed
  *)
  Lemma zbetween_zone_sub_zone_at_ofs z ty sl ofs len :
    wf_zone z ty sl ->
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_of ty) ->
    zbetween_zone z (sub_zone_at_ofs z ofs len).
  Proof.
    move=> hwf.
    case: ofs => [ofs|]; last by (move=> _; apply zbetween_zone_refl).
    move=> /(_ _ refl_equal).
    rewrite /zbetween_zone !zify /=.
    by have := hwf.(wfz_len); lia.
  Qed.

  (* We use [sub_zone_at_ofs z (Some 0)] to manipulate sub-zones of [z].
     Not sure if this a clean way to proceed.
     This lemma is a special case of [zbetween_zone_sub_zone_at_ofs].
  *)
  Lemma zbetween_zone_sub_zone_at_ofs_0 z ty sl :
    wf_zone z ty sl ->
    zbetween_zone z (sub_zone_at_ofs z (Some 0) (size_of ty)).
  Proof.
    move=> hwf.
    apply: (zbetween_zone_sub_zone_at_ofs hwf).
    by move=> _ [<-]; lia.
  Qed.

  Lemma subset_memi i1 i2 n :
    I.subset i1 i2 ->
    I.memi i1 n ->
    I.memi i2 n.
  Proof. by move=> /I.subsetP hsub /I.memiP hmem; apply /I.memiP; lia. Qed.

  Lemma subset_mem bytes i1 i2 :
    I.subset i1 i2 ->
    ByteSet.mem bytes i2 ->
    ByteSet.mem bytes i1.
  Proof.
    move=> hsub /ByteSet.memP hmem; apply /ByteSet.memP.
    by move=> n /(subset_memi hsub) /hmem.
  Qed.

  Lemma check_validP (x : var_i) ofs (* ws *) len sr sr' :
(*     let: len := wsize_size ws in *)
(*     (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot x) -> *)
    check_valid rmap x ofs len = ok (sr, sr') ->
    exists bytes,
    [/\ check_gvalid rmap (mk_lvar x) = Some (sr, bytes),
    sr' = sub_region_at_ofs sr ofs len &
    let isub_ofs := interval_of_zone sr'.(sr_zone) in
    ByteSet.mem bytes isub_ofs].
  Proof.
    rewrite /check_valid /check_gvalid.
    t_xrbindP=> (* hofs *) sr'' /get_sub_regionP -> _ /assertP hmem ? <-; subst sr''.
    by eexists.
  Qed.

  Lemma check_vpkP x vpk ofs len sr sr' :
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot x.(gv)) ->
    get_var_kind pmap x = ok (Some vpk) ->
    check_vpk rmap x.(gv) vpk ofs len = ok (sr, sr') ->
    exists bytes,
      [/\ check_gvalid rmap x = Some (sr, bytes),
      sr' = sub_region_at_ofs sr ofs len &
      let isub_ofs := interval_of_zone sr'.(sr_zone) in
      ByteSet.mem bytes isub_ofs].
  Proof.
    move=> hofs; rewrite /get_var_kind /check_gvalid.
    case : (@idP (is_glob x)) => hg.
    + t_xrbindP=> -[_ ws'] /get_globalP /dup [] /wf_globals /sub_region_glob_wf hwf -> <- /= [<- <-].
(*       set sr' := sub_region_glob _ _. *)
      set bytes := ByteSet.full _.
      exists bytes; split=> //.
      apply: subset_mem; last by apply mem_full.
      rewrite subset_interval_of_zone.
      by apply (zbetween_zone_sub_zone_at_ofs hwf).
    by case hlocal: get_local => [pk|//] [<-] /(check_validP).
  Qed.

  Lemma check_gvalid_wf x sr_bytes :
    wfr_WF rmap ->
    check_gvalid rmap x = Some sr_bytes ->
    wf_sub_region sr_bytes.1 x.(gv).(vtype).
  Proof.
    move=> hwfr.
    rewrite /check_gvalid; case: (@idP (is_glob x)) => hg.
    + by case heq: Mvar.get => [[??]|//] [<-] /=; apply (sub_region_glob_wf (wf_globals heq)).
    by case heq: Mvar.get => // -[<-]; apply hwfr.
  Qed.

  Lemma check_vpk_wordP x vpk ofs ws t :
    (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + wsize_size ws <= size_slot x.(gv)) ->
    get_var_kind pmap x = ok (Some vpk) ->
    check_vpk_word rmap x.(gv) vpk ofs ws = ok t ->
    exists sr bytes,
      [/\ check_gvalid rmap x = Some (sr, bytes),
      let isub_ofs := interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws)) in
      ByteSet.mem bytes isub_ofs &
      is_align (sub_region_addr sr) ws].
  Proof.
    move=> hofs hget.
    rewrite /check_vpk_word.
    t_xrbindP=> -[sr sr'] /(check_vpkP hofs hget) [bytes [hgvalid -> hmem]].
    assert (hwf := check_gvalid_wf wfr_wf hgvalid).
    move=> /(check_alignP hwf) hal.
    by exists sr, bytes.
  Qed.

  (* TODO : prove the same thing for all cases of pk *)
  Lemma sub_region_addr_direct x sl ofs ws z sc :
    wf_direct x sl ofs ws z sc ->
    sub_region_addr (sub_region_direct sl ws sc z) = (wbase_ptr sc + wrepr _ (ofs + z.(z_ofs)))%R.
  Proof.
    by move=> hwf; rewrite /sub_region_addr hwf.(wfd_offset) wrepr_add GRing.addrA.
  Qed.

  (* TODO : prove the same thing for all cases of pk *)
  Lemma sub_region_direct_wf x sl ofs ws z sc :
    wf_direct x sl ofs ws z sc ->
    wf_sub_region (sub_region_direct sl ws sc z) x.(vtype).
  Proof. by case. Qed.

  Lemma sub_region_addr_glob x ofs ws :
    wf_global x ofs ws ->
    sub_region_addr (sub_region_glob x ws) = (rip + wrepr _ ofs)%R.
  Proof.
    move=> hwf.
    by rewrite /sub_region_addr /sub_region_glob /= hwf.(wfg_offset) wrepr0 GRing.addr0.
  Qed.

  Lemma addr_from_pkP (x:var_i) pk sr xi ofs :
    wf_local x pk ->
    valid_pk rmap s' sr pk ->
    addr_from_pk pmap x pk = ok (xi, ofs) ->
    exists w,
      get_var (evm s') xi >>= to_pointer = ok w /\
      sub_region_addr sr = (w + wrepr _ ofs)%R.
  Proof.
    case: pk => //.
    + move=> sl ofs' ws z sc hwfpk /= -> [<- <-].
      rewrite /= /get_gvar /= base_ptrP /= truncate_word_u.
      eexists; split; first by reflexivity.
      rewrite /sub_region_addr /=.
      by rewrite (wfd_offset hwfpk) wrepr_add GRing.addrA.
    move=> p hwfpk /= hpk [<- <-].
    rewrite /= /get_gvar /= hpk /= truncate_word_u.
    eexists; split; first by reflexivity.
    by rewrite wrepr0 GRing.addr0.
  Qed.

  (* If [x] is a local variable *)
  Lemma check_mk_addr_ptr (x:var_i) aa ws xi ei e1 i1 pk sr :
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    wf_local x pk ->
    valid_pk rmap s' sr pk ->
    mk_addr_ptr pmap x aa ws pk e1 = ok (xi, ei) ->
    ∃ (wx wi : u64),
      [/\ Let x := get_var (evm s') xi in to_pointer x = ok wx,
          Let x := sem_pexpr [::] s' ei in to_pointer x = ok wi
        & (sub_region_addr sr + wrepr U64 (i1 * mk_scale aa ws))%R = (wx + wi)%R].
  Proof.
    move=> he1 hwfpk hpk.
    rewrite /mk_addr_ptr.
    t_xrbindP=> -[xi' ofs] haddr <- <-.
    move: haddr => /(addr_from_pkP hwfpk hpk) [wx [-> ->]].
    rewrite (mk_ofsP _ _ _ he1) /= truncate_word_u.
    eexists _, _; split=> //.
    by rewrite Z.add_comm wrepr_add GRing.addrA.
  Qed.

  Definition valid_vpk rv s2 x sr vpk :=
    match vpk with
    | VKglob (_, ws) => sr = sub_region_glob x ws
    | VKptr pk => valid_pk rv s2 sr pk
    end.

  (* A variant of [wfr_PTR] for [gvar]. *)
  (* Is it useful? *)
  Lemma wfr_gptr x sr bytes :
    check_gvalid rmap x = Some (sr, bytes) ->
    exists vpk, get_var_kind pmap x = ok (Some vpk)
    /\ valid_vpk rmap s' x.(gv) sr vpk.
  Proof.
    rewrite /check_gvalid /get_var_kind.
    case: is_glob.
    + case heq: Mvar.get => [[ofs ws]|//] /= [<- _].
      have /get_globalP -> := heq.
      by eexists.
    case heq: Mvar.get => // [sr'] [<- _].
    have /wfr_ptr [pk [-> hpk]] := heq.
    by eexists.
  Qed.

  (* [wf_global] and [wf_direct] in a single predicate. *)
  Definition wf_vpk x vpk :=
    match vpk with
    | VKglob zws => wf_global x zws.1 zws.2
    | VKptr pk => wf_local x pk
    end.

  Lemma get_var_kind_wf x vpk :
    get_var_kind pmap x = ok (Some vpk) ->
    wf_vpk x.(gv) vpk.
  Proof.
    rewrite /get_var_kind.
    case: is_glob.
    + by t_xrbindP=> -[ofs ws] /get_globalP /wf_globals ? <-.
    case heq: get_local => [pk|//] [<-].
    by apply wf_locals.
  Qed.

  Lemma addr_from_vpkP (x:var_i) vpk sr xi ofs :
    wf_vpk x vpk ->
    valid_vpk rmap s' x sr vpk ->
    addr_from_vpk pmap x vpk = ok (xi, ofs) ->
    exists w,
      get_var (evm s') xi >>= to_pointer = ok w /\
      sub_region_addr sr = (w + wrepr _ ofs)%R.
  Proof.
    case: vpk => [[ofs' ws]|pk].
    + move=> hwfpk /= -> [<- <-].
      rewrite /= /get_gvar /= vs_rip /= truncate_word_u.
      eexists; split; first by reflexivity.
      rewrite /sub_region_addr /=.
      by rewrite (wfg_offset hwfpk) wrepr0 GRing.addr0.
    by apply addr_from_pkP.
  Qed.

  Lemma check_mk_addr (x:var_i) aa ws xi ei e1 i1 vpk sr :
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    wf_vpk x vpk ->
    valid_vpk rmap s' x sr vpk ->
    mk_addr pmap x aa ws vpk e1 = ok (xi, ei) ->
    ∃ (wx wi : u64),
      [/\ Let x := get_var (evm s') xi in to_pointer x = ok wx,
          Let x := sem_pexpr [::] s' ei in to_pointer x = ok wi
        & (sub_region_addr sr + wrepr U64 (i1 * mk_scale aa ws))%R = (wx + wi)%R].
  Proof.
    move=> he1 hwfpk hpk.
    rewrite /mk_addr.
    t_xrbindP=> -[xi' ofs] haddr <- <-.
    move: haddr => /(addr_from_vpkP hwfpk hpk) [wx [-> ->]].
    rewrite (mk_ofsP _ _ _ he1) /= truncate_word_u.
    eexists _, _; split=> //.
    by rewrite Z.add_comm wrepr_add GRing.addrA.
  Qed.
(*
  Lemma check_mk_addr x vpk aa ws t xi ei e1 i1 ofs : 
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    0 <= i1 * mk_scale aa ws /\ i1 * mk_scale aa ws + wsize_size ws <= size_slot x.(gv) ->
    WArray.is_align (i1 * mk_scale aa ws) ws ->
    get_var_kind pmap x = ok (Some vpk) ->
    check_vpk_word rmap (gv x) vpk ofs ws = ok t ->
    (ofs <> None -> ofs = Some (i1 * mk_scale aa ws)) ->
    mk_addr pmap (gv x) aa ws vpk e1 = ok (xi, ei) ->
    exists sr bytes wx wi,
    [/\ check_gvalid rmap x = Some (sr, bytes),
        let sub_ofs  := sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws) in
        let isub_ofs := interval_of_zone sub_ofs in
        ByteSet.mem bytes isub_ofs,
        get_var (evm s') xi >>= to_pointer = ok wx,
        sem_pexpr [::] s' ei >>= to_pointer = ok wi &
        (sub_region_addr sr + wrepr Uptr (i1 * mk_scale aa ws)%Z = wx + wi)%R /\
        is_align (wx + wi) ws].
  Proof.
    move=> he1 hi1 hal1; rewrite /get_var_kind /check_vpk_word /mk_addr.
    t_xrbindP => hget sr' hvpk halign hofs haddr.
    have hofs' : ∀ zofs : Z, ofs = Some zofs → 0 <= zofs ∧ zofs + wsize_size ws <= size_slot (gv x).
    + case: (ofs) hofs => [ofs'|//].
      by move=> /(_ ltac:(discriminate)) [->] _ [<-].
    have [sr [bytes [hgvalid ? hmem]]] := check_vpkP hofs' hget hvpk; subst sr'.
    have hwf := check_gvalid_wf hgvalid.
    have hal: is_align (sub_region_addr sr + wrepr _ (i1 * mk_scale aa ws)) ws.
    + change (wsize_size ws) with (size_of (sword ws)) in hofs'.
      move /(check_alignP (sub_region_at_ofs_wf hwf hofs')) : halign.
      case: (ofs) hofs.
      + move=> _ /(_ ltac:(discriminate)) [->].
        by rewrite /sub_region_addr wrepr_add GRing.addrA.
      by move=> _ halign; apply is_align_add => //; apply arr_is_align.
    exists sr, bytes.
    rewrite hgvalid; move: hgvalid; rewrite /check_gvalid.
    case: (@idP (is_glob x)) hget haddr => hglob.
    + t_xrbindP=> -[xofs xws] /get_globalP hget <- [<- <-] /=.
      rewrite hget => -[??]; subst sr bytes.
      exists rip, (wrepr _ xofs + wrepr _ (i1 * mk_scale aa ws))%R.
      rewrite vs_rip (mk_ofsP aa ws xofs he1) /= !truncate_word_u wrepr_add GRing.addrC.
      split=> //.
      by move: hal; rewrite (sub_region_addr_glob (wf_globals hget)) GRing.addrA.
    case heq: get_local => [pk|//] [<-] /(check_mk_addr_ptr he1 heq) haddr.
    case hsr: Mvar.get => [sr1|//] [??]; subst sr1 bytes.
    have [pk' []] := wfr_ptr hsr; rewrite heq => -[<-] /haddr [wx [wi [-> -> heq1]]].
    by exists wx, wi; split=> //; rewrite -heq1.
  Qed.
*)
 
  Lemma sub_region_addr_offset len sr ofs :
    (sub_region_addr sr + wrepr _ ofs)%R =
    sub_region_addr (sub_region_at_ofs sr (Some ofs) len).
  Proof. by rewrite /sub_region_addr wrepr_add GRing.addrA. Qed.

  Lemma no_overflow_incl p1 sz1 p2 sz2 :
    zbetween p1 sz1 p2 sz2 ->
    no_overflow p1 sz1 ->
    no_overflow p2 sz2.
  Proof. by rewrite /zbetween /no_overflow !zify; lia. Qed.

  Lemma no_overflow_sub_region_addr sr ty :
    wf_sub_region sr ty ->
    no_overflow (sub_region_addr sr) (size_of ty).
  Proof.
    move=> hwf; apply (no_overflow_incl (zbetween_sub_region_addr hwf)).
    by apply (addr_no_overflow hwf.(wfr_slot)).
  Qed.

  Lemma validw_sub_region_addr sr ws :
    wf_sub_region sr (sword ws) ->
    is_align (sub_region_addr sr) ws ->
    validw (emem s') (sub_region_addr sr) ws.
  Proof.
    move=> hwf hal.
    have hptr := vs_slot_valid (valid_state:=hvalid) hwf.(wfr_slot).
    apply /validwP; split=> //.
    move=> k hk; apply hptr; move: hk.
    apply between_byte.
    + by apply (no_overflow_sub_region_addr hwf).
    apply (zbetween_sub_region_addr hwf).
  Qed.

  Lemma validw_sub_region_at_ofs sr ty ofs ws :
    wf_sub_region sr ty ->
    0 <= ofs /\ ofs + wsize_size ws <= size_of ty ->
    is_align (sub_region_addr sr + wrepr _ ofs)%R ws ->
    validw (emem s') (sub_region_addr sr + wrepr _ ofs)%R ws.
  Proof.
    move=> hwf hbound.
    have hofs: forall zofs : Z, Some ofs = Some zofs ->
      0 <= zofs /\ zofs + size_of (sword ws) <= size_of ty.
    + by move=> _ [<-].
    have hwf' := sub_region_at_ofs_wf hwf hofs.
    rewrite (sub_region_addr_offset (wsize_size ws)).
    by apply (validw_sub_region_addr hwf').
  Qed.

  Lemma memi_mem_U8 bytes z off :
    ByteSet.memi bytes (z.(z_ofs) + off) =
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs z (Some off) (wsize_size U8))).
  Proof.
    apply /idP/idP.
    + move=> hmem; apply /ByteSet.memP; move=> i.
      rewrite /interval_of_zone /I.memi /= wsize8 !zify => hbound.
      by have -> : i = z_ofs z + off by lia.
    move=> /ByteSet.memP; apply.
    by rewrite /interval_of_zone /I.memi /= wsize8 !zify; lia.
  Qed.

  Lemma sub_zone_at_ofs_compose z ofs1 ofs2 len1 len2 :
    sub_zone_at_ofs (sub_zone_at_ofs z (Some ofs1) len1) (Some ofs2) len2 =
    sub_zone_at_ofs z (Some (ofs1 + ofs2)) len2.
  Proof. by rewrite /= Z.add_assoc. Qed.

  (* On the model of [between_byte]. *)
  Lemma zbetween_zone_byte z1 z2 i :
    zbetween_zone z1 z2 ->
    0 <= i /\ i < z2.(z_len) ->
    zbetween_zone z1 (sub_zone_at_ofs z2 (Some i) (wsize_size U8)).
  Proof. by rewrite /zbetween_zone wsize8 !zify /=; lia. Qed.

  Lemma zbetween_zone_sub_zone_at_ofs_option z i ofs len ty sl :
    wf_zone z ty sl ->
    0 <= i /\ i + len <= size_of ty ->
    (ofs <> None -> ofs = Some i) ->
    zbetween_zone (sub_zone_at_ofs z ofs len) (sub_zone_at_ofs z (Some i) len).
  Proof.
    move=> hwf hi.
    case: ofs => [ofs|].
    + by move=> /(_ ltac:(discriminate)) [->]; apply zbetween_zone_refl.
    move=> _.
    apply (zbetween_zone_sub_zone_at_ofs hwf).
    by move=> _ [<-].
  Qed.

(*
  Lemma get_read_mem (* v *) sr bytes ws w :
    wf_sub_region sr (sword ws) ->
    eq_sub_region_val (emem s') sr bytes (Vword w) ->
    ByteSet.mem bytes (interval_of_zone sr.(sr_zone)) ->
(*     get_val ws v 0 = ok w -> *)
    is_align (sub_region_addr sr) ws ->
    read_mem (emem s') (sub_region_addr sr) ws = ok w.
  Proof.
  Admitted.
*)
(* TODO: relire cette preuve pour voir si les hypothèses sont indispensables
   et les plus logiques.
   On voudrait ne pas utiliser lia !
   Peut-on faire un premier lemme sans ofs, juste pour les Vword ws ?
   Et ensuite un 2ème lemme qui parle de n'importe quel sr dont on prend
   ws ? (cf validw_sub_region_addr et validw_sub_region_at_ofs)

   Intuition du lemme : eq_sub_region_val donne correspondance entre lire
   dans v et lire dans la mémoire, mais seulement pour des bytes.
   On montre que c'est aussi vrai pour n'importe quelle taille [ws] de lecture.
*)
(* TODO : wsize_size et size_of dans positive ? Pour éviter les Z2Pos.id *)
(*
  Lemma get_val_read (v : value) sr bytes ofs ws aa i w :
    wf_sub_region sr (type_of_val v) ->
    eq_sub_region_val_read (emem s') sr bytes v ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws))) ->
    (ofs <> None -> ofs = Some (i * mk_scale aa ws)) ->
    get_val aa ws v i = ok w ->
    is_align (sub_region_addr sr) ws ->
    read (emem s') (sub_region_addr sr + wrepr _ (i * mk_scale aa ws))%R ws = ok w.
  Proof.
    move=> hwf hread hmem hofs.
    rewrite /get_val; t_xrbindP=> a ha hget hal.
    have := WArray.get_bound hget; rewrite Z2Pos.id; last by apply size_of_gt0.
    move=> [h1 h2 hal'].
    rewrite (read8_read (v:=w)).
    + by rewrite (is_align_addE hal) arr_is_align hal'.
    move=> k hk.
    rewrite addE -GRing.addrA -wrepr_add.
    apply hread.
    + rewrite memi_mem_U8; apply: subset_mem hmem; rewrite subset_interval_of_zone.
      rewrite -(sub_zone_at_ofs_compose _ _ _ (wsize_size ws)).
      apply: zbetween_zone_byte => //.
      by apply (zbetween_zone_sub_zone_at_ofs_option hwf).
    rewrite /get_val_byte /get_val ha /= WArray.get8_read.
    by have [_] := read_read8 hget; apply.
  Qed.
*)
  Lemma eq_sub_region_val_read_word sr ty (v : value) bytes ofs ws i w :
    wf_sub_region sr ty ->
    eq_sub_region_val_read (emem s') sr bytes v ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws))) ->
    (ofs <> None -> ofs = Some i) ->
    0 <= i /\ i + wsize_size ws <= size_of ty ->
    (forall k, 0 <= k < wsize_size ws -> get_val_byte v (i + k) = ok (LE.wread8 w k)) ->
    read (emem s') (sub_region_addr sr + wrepr _ i)%R ws =
      if is_align (sub_region_addr sr + wrepr _ i)%R ws then ok w else Error ErrAddrInvalid.
  Proof.
    move=> hwf hread hmem hofs hbound hget.
    apply read8_read.
    move=> k hk.
    rewrite addE -GRing.addrA -wrepr_add.
    apply hread; last by apply hget.
    rewrite memi_mem_U8; apply: subset_mem hmem; rewrite subset_interval_of_zone.
    rewrite -(sub_zone_at_ofs_compose _ _ _ (wsize_size ws)).
    apply: zbetween_zone_byte => //.
    by apply (zbetween_zone_sub_zone_at_ofs_option hwf).
  Qed.

(*
  Lemma get_arr_read_mem (n:positive) (t : WArray.array n) sr bytes ofs aa ws i w :
    wf_sub_region sr (sarr n) ->
    eq_sub_region_val (sarr n) (emem s') sr bytes (Varr t) ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs (wsize_size ws))) ->
    (ofs <> None -> ofs = Some (i * mk_scale aa ws)) ->
    WArray.get aa ws t i = ok w ->
    is_align (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws)) ws ->
    read_mem (emem s') (sub_region_addr sr + wrepr U64 (i * mk_scale aa ws)) ws = ok w.
  Proof.
    move=> hwf heq (* hgvalid *) hmem hofs hget hal.
    rewrite Memory.readP /CoreMem.read.
    have [hbound1 hbound2 _] := WArray.get_bound hget.
    have := valid_pointer_sub_region_at_ofs hwf (conj hbound1 hbound2) hal.
    rewrite -validr_valid_pointer => /is_okP [?] /= => hv; rewrite hv /=.
    move: (hget);rewrite /WArray.get /CoreMem.read; t_xrbindP => ? _ <-.
    do 2 f_equal; rewrite /CoreMem.uread.
    apply eq_map_ziota => k hk /=.
    have [v hget8]:= WArray.get_get8 AAscale hget hk.
    have /WArray.get_uget -> := hget8.
    move /heq: hget8; rewrite Memory.readP /CoreMem.read.
    have h: 0 <= i * mk_scale aa ws + k ∧ i * mk_scale aa ws + k < n by lia.
    have h1: ByteSet.memi bytes (sr.(sr_zone).(z_ofs) + (i * mk_scale aa ws + k)).
    + move /ByteSet.memP : hmem; apply.
      rewrite /I.memi /= !zify.
      case: ofs hofs => [ofs|_].
      + by move=> /(_ ltac:(discriminate)) [->] /=; lia.
      by have /= hlen := hwf.(wfz_len); lia.
    move=> /(_ h h1){h h1}; t_xrbindP => ? hvr.
    by rewrite CoreMem.uread8_get addE wrepr_add GRing.addrA.
  Qed.

  Lemma get_word_read_mem ws (w : word ws) sr bytes:
    wf_sub_region sr (sword ws) ->
    eq_sub_region_val (sword ws) (emem s') sr bytes (Vword w) ->
    ByteSet.mem bytes (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) (Some 0)%Z (wsize_size ws))) ->
    is_align (sub_region_addr sr) ws ->
    read_mem (emem s') (sub_region_addr sr) ws = ok w.
  Proof.
    move=> hwf heq hmem hal.
    have [t ht] : exists t, WArray.set (WArray.empty (Z.to_pos (wsize_size ws))) AAscale 0 w = ok t.
    + rewrite /WArray.set CoreMem.write_uwrite; first by eexists; reflexivity.
      change (validw (WArray.empty (Z.to_pos (wsize_size ws))) (0 * mk_scale AAscale ws) ws)
        with (WArray.validw (WArray.empty (Z.to_pos (wsize_size ws))) (0 * mk_scale AAscale ws) ws).
      by rewrite /WArray.validw /WArray.in_range /= Z.leb_refl.
    have hwf': wf_sub_region sr (sarr (Z.to_pos (wsize_size ws))).
    + by case: hwf => ? [*]; split.
    have heq': eq_sub_region_val (sarr (Z.to_pos (wsize_size ws))) (emem s') sr bytes (Varr t).
    + move=> off hoff hmem' w' hval.
      apply heq => //.
      by rewrite /get_val_byte /get_val /array_of_val ht.
    have := get_arr_read_mem (t := t) (sr:=sr) hwf' heq' hmem _ (WArray.setP_eq ht).
    rewrite /= wrepr0 GRing.addr0.
    by apply.
  Qed.
*)

  Let X e : Prop :=
    ∀ e' v,
      alloc_e pmap rmap e = ok e' →
      sem_pexpr gd s e = ok v →
      sem_pexpr [::] s' e' = ok v.

  Let Y es : Prop :=
    ∀ es' vs,
      alloc_es pmap rmap es = ok es' →
      sem_pexprs gd s es = ok vs →
      sem_pexprs [::] s' es' = ok vs.

  Lemma check_varP (x:var_i) t: 
    check_var pmap x = ok t -> 
    get_var_kind pmap (mk_lvar x) = ok None.
  Proof. by rewrite /check_var /get_var_kind /=; case: get_local. Qed.

(* [type_of_get_var] is not precise enough. We need the fact that [v] is
   necessarily of the form [Vword w] (i.e. is not [Vundef]).
*)
Lemma get_gvar_word x ws gd vm v :
  x.(gv).(vtype) = sword ws ->
  get_gvar gd vm x = ok v ->
  exists (ws' : wsize) (w : word ws'), (ws' <= ws)%CMP /\ v = Vword w.
Proof.
  move=> hty; rewrite /get_gvar.
  case: (is_lvar x).
  + rewrite /get_var; apply : on_vuP => // t _ <-.
    move: t; rewrite hty => t /=.
    by eexists _, _; split; first by apply pw_proof.
  move=> /get_globalI [gv [_]]; rewrite hty.
  case: gv => ?? -> // [<-].
  by eexists _, _; split.
Qed.

(* [psem.type_of_val_word] could be much more precise. *)
Lemma type_of_val_word :
∀ (v : value) (wz : wsize),
  type_of_val v = sword wz
  → (wz = U8 /\ exists wz', v = undef_w wz') ∨ (∃ w : word wz, v = Vword w).
Proof.
  move=> v wz.
  case: v => //=.
  + move=> wz' w [?]; subst wz'. right. eauto.
  move=> [] //= wz' heq [<-]. left. split=> //.
  rewrite (Eqdep_dec.UIP_refl_bool _ heq). eexists. reflexivity.
Qed.

Lemma get_val_byte_word ws (w : word ws) off :
  0 <= off < wsize_size ws ->
  get_val_byte (Vword w) off = ok (LE.wread8 w off).
Proof. by rewrite /= -!zify => ->. Qed.

(*
(* If we read a large enough sub-word, we get the full word. *)
Lemma get_val_word aa ws w :
  get_val aa ws (Vword w) 0 = ok w.
Proof.
  rewrite /get_val /array_of_val.
  set empty := WArray.empty _.
  have [t ht] : exists t, WArray.set empty AAscale 0 w = ok t.
  + apply /writeV.
    rewrite WArray.validw_in_range WArray.is_align_scale /WArray.in_range !zify.
    by rewrite Z2Pos.id //; lia.
  by rewrite ht; apply (WArray.setP_eq ht).
Qed.

Lemma get_val_array n aa ws (a : WArray.array n) i :
  get_val aa ws (Varr a) i = WArray.get aa ws a i.
Proof. by []. Qed.
*)
Lemma sub_region_at_ofs_None sr len :
  sub_region_at_ofs sr None len = sr.
Proof. by case: sr. Qed.

Lemma check_diffP x t : check_diff pmap x = ok t -> ~Sv.In x (vnew pmap).
Proof. by rewrite /check_diff; case:ifPn => /Sv_memP. Qed.

(* Maybe overkill? *)
Lemma ofs_bound_option z len size ofs :
  0 <= z /\ z + len <= size ->
  (ofs <> None -> ofs = Some z) ->
  forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size.
Proof.
  move=> hbound.
  case: ofs => //.
  by move=> _ /(_ ltac:(discriminate)) [->] _ [<-].
Qed.

(* TODO: open GRing *)
  Lemma check_e_esP : (∀ e, X e) * (∀ es, Y es).
  Proof.
    apply: pexprs_ind_pair; subst X Y; split => //=.
    + by move=> ?? [<-] [<-].
    + move=> e he es hes ??; t_xrbindP => e' /he{he}he es' /hes{hes}hes <- /=.
      by move=> v /he -> vs /hes -> <-.
    + by move=> z ?? [<-] [<-].
    + by move=> b ?? [<-] [<-].
    + by move=> n ?? [<-] [<-].
    + move=> x e' v; t_xrbindP => -[ vpk | ] hgvk; last first.
      + by t_xrbindP=> _ /check_diffP hnnew <-; apply: get_var_kindP.
      case hty: is_word_type => [ws | //]; move /is_word_typeP in hty.
      t_xrbindP => ? hcheck [xi ei] haddr <- hget /=.
      have h0: Let x := sem_pexpr [::] s' 0 in to_int x = ok 0 by done.
      have h1: 0 <= 0 /\ wsize_size ws <= size_slot x.(gv).
      + by rewrite hty /=; lia.
      have h1' := ofs_bound_option h1 (fun _ => refl_equal).
      have [sr [bytes [hgvalid hmem halign]]] := check_vpk_wordP h1' hgvk hcheck.
      have h2: valid_vpk rmap s' x.(gv) sr vpk.
      + have := wfr_gptr hgvalid.
        by rewrite hgvk => -[_ [[]] <-].
      have [wx [wi [-> -> /= haddr2]]] := check_mk_addr h0 (get_var_kind_wf hgvk) h2 haddr.
      rewrite -haddr2.
      assert (heq := wfr_val hgvalid hget); rewrite hty in heq.
      case: heq => hread hty'.
      assert (hwf := check_gvalid_wf wfr_wf hgvalid).
      have [ws' [w [_ ?]]] := get_gvar_word hty hget; subst v.
      case: hty' => ?; subst ws'.
      rewrite (eq_sub_region_val_read_word hwf hread hmem _ h1 (get_val_byte_word w) (w:=w)) //.
      by rewrite wrepr0 GRing.addr0 halign.
    + move=> aa sz x e1 he1 e' v he'; apply: on_arr_gvarP => n t hty /= hget.
      t_xrbindP => i vi /he1{he1}he1 hvi w hw <-.
      move: he'; t_xrbindP => e1' /he1{he1}he1'.
      have h0 : sem_pexpr [::] s' e1' >>= to_int = ok i.
      + by rewrite he1'.
      move=> [vpk | ]; last first.
      + t_xrbindP => h _ /check_diffP h1 <- /=.
        by rewrite (get_var_kindP h h1 hget) /= h0 /= hw.
      t_xrbindP => hgvk ? hcheck [xi ei] haddr <- /=.
      have [h1 h2 h3] := WArray.get_bound hw.
      have h4: 0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + wsize_size sz <= size_slot x.(gv).
      + by rewrite hty.
      have h4' := ofs_bound_option h4 (mk_ofsiP h0).
      have [sr [bytes [hgvalid hmem halign]]] := check_vpk_wordP h4' hgvk hcheck.
      have h5: valid_vpk rmap s' x.(gv) sr vpk.
      + have := wfr_gptr hgvalid.
        by rewrite hgvk => -[_ [[]] <-].
      have [wx [wi [-> -> /= haddr2]]] := check_mk_addr h0 (get_var_kind_wf hgvk) h5 haddr.
      rewrite -haddr2.
      assert (heq := wfr_val hgvalid hget).
      case: heq => hread _.
      assert (hwf := check_gvalid_wf wfr_wf hgvalid).
      have [_ h6] := (read_read8 hw).
      rewrite (eq_sub_region_val_read_word hwf hread hmem (mk_ofsiP h0) (w:=w)) //.
      by rewrite (is_align_addE halign) WArray.arr_is_align h3.
    + move=> sz1 v1 e1 IH e2 v.
      t_xrbindP => _ /check_varP hc _ /check_diffP hnnew e1' /IH hrec <- wv1 vv1 /= hget hto' we1 ve1.
      move=> /hrec -> hto wr hr ?; subst v.
      have := get_var_kindP hc hnnew hget; rewrite /get_gvar /= => -> /=.
      by rewrite hto' hto /= -(eq_mem_source_word hvalid (readV hr)) hr.
    + move=> o1 e1 IH e2 v.
      by t_xrbindP => e1' /IH hrec <- ve1 /hrec /= ->.
    + move=> o1 e1 H1 e1' H1' e2 v.
      by t_xrbindP => e1_ /H1 hrec e1'_ /H1' hrec' <- ve1 /hrec /= -> /= ve2 /hrec' ->.
    + move => e1 es1 H1 e2 v.
      t_xrbindP => es1' /H1{H1}H1 <- vs /H1{H1} /=.
      by rewrite /sem_pexprs => ->.
    move=> t e He e1 H1 e1' H1' e2 v.
    t_xrbindP => e_ /He he e1_ /H1 hrec e1'_ /H1' hrec' <-.
    by move=> b vb /he /= -> /= -> ?? /hrec -> /= -> ?? /hrec' -> /= -> /= ->.
  Qed.

  Definition alloc_eP := check_e_esP.1.
  Definition alloc_esP := check_e_esP.2.

End EXPR.

Lemma get_var_eq x vm v : get_var vm.[x <- v] x = on_vu (pto_val (t:=vtype x)) undef_error v.
Proof. by rewrite /get_var Fv.setP_eq. Qed.

Lemma get_var_neq x y vm v : x <> y -> get_var vm.[x <- v] y = get_var vm y.
Proof. by move=> /eqP h; rewrite /get_var Fv.setP_neq. Qed.

Lemma get_var_set_eq vm1 vm2 (x y : var) v: 
  get_var vm1 y = get_var vm2 y ->
  get_var vm1.[x <- v] y = get_var vm2.[x <- v] y.
Proof.
  by case:( x =P y) => [<- | hne]; rewrite !(get_var_eq, get_var_neq).
Qed.

Lemma is_lvar_is_glob x : is_lvar x = ~~is_glob x.
Proof. by case: x => ? []. Qed.

Lemma get_gvar_eq gd x vm v : 
  ~is_glob x -> get_gvar gd vm.[gv x <- v] x = on_vu (pto_val (t:=vtype (gv x))) undef_error v.
Proof. 
  by move=> /negP => h; rewrite /get_gvar is_lvar_is_glob h get_var_eq.
Qed.

Lemma get_gvar_neq gd (x:var) y vm v : (~is_glob y -> x <> (gv y)) -> get_gvar gd vm.[x <- v] y = get_gvar gd vm y.
Proof. 
  move=> h; rewrite /get_gvar is_lvar_is_glob. 
  by case: negP => // hg; rewrite get_var_neq //; apply h.
Qed.

Lemma get_gvar_set_eq gd vm1 vm2 x y v: 
  get_gvar gd vm1 y = get_gvar gd vm2 y ->
  get_gvar gd vm1.[x <- v] y = get_gvar gd vm2.[x <- v] y.
Proof.
  case : (@idP (is_glob y)) => hg; first by rewrite !get_gvar_neq.
  case:( x =P (gv y)) => heq; last by rewrite !get_gvar_neq.
  by move: v; rewrite heq => v; rewrite !get_gvar_eq.
Qed.

Lemma get_localn_checkg_diff rmap sr_bytes s2 x y : 
  get_local pmap x = None ->
  wfr_PTR rmap s2 ->
  check_gvalid rmap y = Some sr_bytes ->
  (~is_glob y -> x <> (gv y)).
Proof.
  rewrite /check_gvalid; case:is_glob => // hl hwf.
  case heq: Mvar.get => [sr' | // ] _ _.
  by have /hwf [pk [hy _]] := heq; congruence.
Qed.

Lemma valid_state_set_var rmap m0 s1 s2 x v:
  valid_state rmap m0 s1 s2 ->
  get_local pmap x = None ->
  ¬ Sv.In x (vnew pmap) ->
  valid_state rmap m0 (with_vm s1 (evm s1).[x <- v]) (with_vm s2 (evm s2).[x <- v]).
Proof.
  case: s1 s2 => mem1 vm1 [mem2 vm2] [/=] hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem hget hnin.
  constructor => //=.
  + by rewrite get_var_neq //; assert (h:=rip_in_new); SvD.fsetdec.
  + by rewrite get_var_neq //; assert (h:=rsp_in_new); SvD.fsetdec.
  + by move=> y hy hnnew; apply get_var_set_eq; apply heqvm.
  rewrite /with_vm /=; case: hwfr => hwfsr hval hptr.
  constructor => //.
  + move=> y sr bytes vy hy; have ? := get_localn_checkg_diff hget hptr hy.
    by rewrite get_gvar_neq //; apply hval.
  move=> y mp hy; have [pk [hgety hpk]]:= hptr y mp hy; exists pk; split => //.
  case: pk hgety hpk => //= yp hyp.
  assert (h := wfr_new (wf_locals hyp)).
  by rewrite get_var_neq //; SvD.fsetdec.
Qed.
(*
(* Qu'est-ce que rset_word ? *)
Lemma set_wordP rmap x sr ws rmap': 
  set_word rmap x sr ws = ok rmap' ->
  exists sr',
  check_gvalid 
  [/\ Mvar.get (var_region rmap) x = Some sr,
      mp_s mp = MSstack, 
      is_align (wrepr Uptr (mp_ofs mp)) ws &
      wf_region
      Align
      rmap' = rset_word rmap x mp]. 
Proof.
  rewrite /set_word.
  case heq : Mvar.get => [ [[] ofs] | ] //=.
  t_xrbindP => ? /assertP hal <-.
  by eexists; split; first reflexivity.
Qed.
*)

Lemma wsize_size_le ws ws': (ws ≤ ws')%CMP -> (wsize_size ws <= wsize_size ws').
Proof. by case: ws ws' => -[]. Qed.

Lemma size_of_le ty ty' : subtype ty ty' -> size_of ty <= size_of ty'.
Proof.
  case: ty => [||p|ws]; case:ty' => [||p'|ws'] //.
  + by move=> /ZleP.
  by apply wsize_size_le.
Qed.
(*
Lemma check_gvalid_rset_word rmap x y mp mpy: 
  mp_s mp = MSstack ->
  Mvar.get (var_region rmap) x = Some mp ->
  check_gvalid (rset_word rmap x mp) y = Some mpy ->
  [/\ ~is_glob y, x = (gv y) & mp = mpy] \/ 
  [/\ (~is_glob y -> x <> gv y), mp <> mpy &check_gvalid rmap y = Some mpy].
Proof.
  rewrite /check_gvalid /rset_word => hmps hgx.
  case:ifPn => ?.
  + move=> h; right;split => //.
    by case: Mvar.get h => // ? [<-] => ?; subst mp.
  case heq : check_valid => [mp1 | //] [?]; subst mp1.
  move:heq; rewrite check_validP => /= -[hgy [xs []]].
  rewrite Mmp.setP; case: eqP => [? [?]| ].
  + by subst mpy xs => /SvD.F.singleton_iff ?; left.
  move=> hd hg /Sv_memP hin; right; split => //.
  + by move=> _ ?; subst x; apply hd; move: hgy;rewrite hgx => -[].
  by rewrite /check_valid hgy hg hin.
Qed.

Lemma get_global_pos x ofs: 
  get_global pmap x = ok ofs ->
  global_pos x = Some (ofs, vtype x).
Proof. by rewrite get_globalP /global_pos => ->. Qed.

Lemma get_local_pos x ofs:
  get_local pmap x = Some (Pstack ofs) ->
  local_pos x = Some (ofs, vtype x).
Proof. by rewrite /local_pos => ->. Qed.

Lemma valid_mp_bound mp ty : 
  valid_mp mp ty ->
  0 <= mp_ofs mp ∧ 
  mp_ofs mp + size_of ty <= wptr_size (mp_s mp).
Proof.
  move=> [x [/size_of_le hsub hv]].
  case: eqP hv => heq.
  + rewrite heq => /get_global_pos hgp. 
    assert (h:= wfg_ofs wf_globals hgp); rewrite /wptr_size /=; lia.
  move=> /get_local_pos hgx.
  assert (h:= wfg_ofs wf_locals hgx).
  have -> : mp_s mp = MSstack by case: (mp_s mp) heq.
  rewrite /wptr_size /=; lia.
Qed.

Lemma valid_mp_addr mp ty: 
  valid_mp mp ty ->
  wunsigned (mp_addr mp) = wunsigned (wptr (mp_s mp)) + (mp_ofs mp).
Proof.
  move=> /valid_mp_bound; rewrite /mp_addr => h.
  apply wunsigned_add; have ? := gt0_size_of ty.
  have := @ge0_wunsigned Uptr (wptr (mp_s mp)).
  by case: (mp_s mp) h; rewrite /wptr /wptr_size /=; lia.
Qed.

Lemma valid_mp_addr_bound mp ty: 
  valid_mp mp ty ->
  wunsigned (wptr (mp_s mp)) <= wunsigned (mp_addr mp) /\
  wunsigned (mp_addr mp) + size_of ty <= wunsigned (wptr (mp_s mp)) + wptr_size (mp_s mp).
Proof.
  move=> h; rewrite (valid_mp_addr h); have := (valid_mp_bound h); lia.
Qed.

Lemma ms_bound s : wunsigned (wptr s) + wptr_size s <= wbase Uptr.
Proof. by case: s. Qed.
*)

(* TODO : move (and rename?) *)
Lemma zbetween_refl p sz : zbetween p sz p sz.
Proof. by rewrite /zbetween !zify; lia. Qed.

(* TODO : move *)
Lemma disjoint_zrange_incl p1 s1 p2 s2 p1' s1' p2' s2' :
  zbetween p1 s1 p1' s1' ->
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2' s2'.
Proof.
  rewrite /zbetween /disjoint_zrange /no_overflow !zify.
  by move=> ?? [/ZleP ? /ZleP ? ?]; split; rewrite ?zify; lia.
Qed.

(* TODO : move *)
Lemma disjoint_zrange_incl_l p1 s1 p2 s2 p1' s1' :
  zbetween p1 s1 p1' s1' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2 s2.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

(* TODO : move *)
Lemma disjoint_zrange_incl_r p1 s1 p2 s2 p2' s2' :
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1 s1 p2' s2'.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

(* Could be an alternative definition for [between_byte]. They are equivalent
   thanks to [zbetween_trans] and [zbetween_refl].
*)
Lemma between_byte pstk sz i  :
  no_overflow pstk sz →
  0 <= i /\ i < sz ->
  between pstk sz (pstk + wrepr U64 i) U8.
Proof.
  rewrite /between /zbetween /no_overflow !zify wsize8 => novf i_range.
  rewrite wunsigned_add; first lia.
  by move: (wunsigned_range pstk); lia.
Abort.

Lemma disjoint_zrange_byte p1 sz1 p2 sz2 i :
  disjoint_zrange p1 sz1 p2 sz2 ->
  0 <= i /\ i < sz2 ->
  disjoint_zrange p1 sz1 (p2 + wrepr _ i) (wsize_size U8).
Proof.
  move=> hd hrange.
  case: (hd) => _ hover _.
  apply: disjoint_zrange_incl_r hd.
  apply: (between_byte hover) => //.
  by apply zbetween_refl.
Qed.

Lemma get_val_byte_bound v off w :
  get_val_byte v off = ok w -> 0 <= off /\ off < size_val v.
Proof.
  case: v => //.
  + move=> len a /=.
    by rewrite -get_read8 => /WArray.get_valid8 /WArray.in_boundP.
  move=> ws w' /=.
  by case: ifP => //; rewrite !zify.
Qed.

Lemma eq_sub_region_val_disjoint_zrange sr bytes ty mem1 mem2 v p sz :
  (forall p1 ws1,
    disjoint_zrange p sz p1 (wsize_size ws1) ->
    read mem2 p1 ws1 = read mem1 p1 ws1) ->
  disjoint_zrange p sz (sub_region_addr sr) (size_of ty) ->
  eq_sub_region_val ty mem1 sr bytes v ->
  eq_sub_region_val ty mem2 sr bytes v.
Proof.
  move=> hreadeq hd [hread hty]; split=> // off hmem w' hget.
  rewrite -(hread _ hmem _ hget).
  apply hreadeq.
  apply (disjoint_zrange_byte hd).
  rewrite -hty.
  by apply (get_val_byte_bound hget).
Qed.

(*
Lemma valid_mp_disjoint mp1 mp2 ty1 ty2: 
  wf_sub_region mp1 ty1 -> 
  wf_sub_region mp2 ty2 ->
  mp1 <> mp2 -> 
  wunsigned (sub_region_addr mp1) + size_of ty1 <= wunsigned (sub_region_addr mp2) ∨ 
  wunsigned (sub_region_addr mp2) + size_of ty2 <= wunsigned (sub_region_addr mp1).
Proof.
  move=> h1 h2; rewrite (wunsigned_sub_region_addr h1) (wunsigned_sub_region_addr h2).
  case: mp1 mp2 h1 h2 => [ms1 ofs1] [ms2 ofs2].
  move=> [x1 [/size_of_le hle1 /= hget1]] [x2 [/size_of_le hle2 /= hget2]].
  have ? := gt0_size_of (vtype x1); have ? := gt0_size_of (vtype x2).
  assert (wfg := wf_globals); assert (wfl := wf_locals).
  case: ms1 hget1 => /= [/get_global_pos | /get_local_pos] h1.
  + have hg1 := wfg_ofs wfg h1; have hg2 := wfg_disj wfg _ h1.
    case: ms2 hget2 => /= [/get_global_pos | /get_local_pos] h2 hd.
    + have hxd: x1 <> x2 by move=> h;apply hd; move: h2; rewrite -h h1 => -[->].
      by have:= hg2 _ _ _ hxd h2; lia.
    have hl2:=  wfg_ofs wfl h2; rewrite /wptr /wptr_size /=; lia.
  have hl1 := wfg_ofs wfl h1; have hl2 := wfg_disj wfl _ h1.
  case: ms2 hget2 => /= [/get_global_pos | /get_local_pos] h2 hd.
  + have hg2:=  wfg_ofs wfg h2; rewrite /wptr /wptr_size /=; lia.
  have hxd: x1 <> x2 by move=> h;apply hd; move: h2; rewrite -h h1 => -[->].
  by have:= hl2 _ _ _ hxd h2; lia.
Qed.
*)

(* TODO: move *)
Lemma disjoint_zrange_sym p1 sz1 p2 sz2 :
  disjoint_zrange p1 sz1 p2 sz2 ->
  disjoint_zrange p2 sz2 p1 sz1.
Proof.
  rewrite /disjoint_zrange; move=> [*]; split=> //; lia.
Qed.

Lemma wf_region_slot_inj r1 r2 :
  wf_region r1 -> wf_region r2 ->
  r1.(r_slot) = r2.(r_slot) ->
  r1 = r2.
Proof.
  move=> hwf1 hwf2.
  have := hwf1.(wfr_align).
  have := hwf2.(wfr_align).
  have := hwf1.(wfr_writable).
  have := hwf2.(wfr_writable).
  by case: (r1); case: (r2) => /=; congruence.
Qed.

Lemma eq_sub_region_val_disjoint_regions s2 sr ty sry ty' mem2 bytes v :
  wf_sub_region sr ty ->
  wf_sub_region sry ty' ->
  sr.(sr_region) <> sry.(sr_region) ->
  sr.(sr_region).(r_writable) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  eq_sub_region_val ty' (emem s2) sry bytes v ->
  eq_sub_region_val ty' mem2 sry bytes v.
Proof.
  move=> hwf hwfy hneq hw hreadeq.
  apply (eq_sub_region_val_disjoint_zrange hreadeq).
  apply (disjoint_zrange_incl (zbetween_sub_region_addr hwf) (zbetween_sub_region_addr hwfy)).
  apply (disjoint_writable hwf.(wfr_slot) hwfy.(wfr_slot)); last by rewrite hwf.(wfr_writable).
  by move=> /(wf_region_slot_inj hwf hwfy).
Qed.

Lemma disjoint_zones_disjoint_zrange sr1 ty1 sr2 ty2 :
  wf_sub_region sr1 ty1 ->
  wf_sub_region sr2 ty2 ->
  sr1.(sr_region) = sr2.(sr_region) ->
  disjoint_zones (sub_zone_at_ofs sr1.(sr_zone) (Some 0) (size_of ty1))
                 (sub_zone_at_ofs sr2.(sr_zone) (Some 0) (size_of ty2)) ->
  disjoint_zrange (sub_region_addr sr1) (size_of ty1) (sub_region_addr sr2) (size_of ty2).
Proof.
  move=> hwf1 hwf2 heq.
  have := addr_no_overflow (wfr_slot hwf1).
  have := addr_no_overflow (wfr_slot hwf2).
  rewrite /disjoint_zones /disjoint_range /disjoint_zrange /no_overflow !Zcmp_le !zify /=.
  rewrite (wunsigned_sub_region_addr hwf1) (wunsigned_sub_region_addr hwf2).
  have /= := wfz_len hwf1.
  have /= := wfz_len hwf2.
  have := wfz_ofs hwf1.
  have := wfz_ofs hwf2.
  rewrite heq.
  by split; rewrite ?zify; lia.
Qed.

Definition disjoint_intervals i1 i2 := I.is_empty (I.inter i1 i2).

Lemma interE i1 i2 n : I.memi (I.inter i1 i2) n = I.memi i1 n && I.memi i2 n.
Proof.
  by rewrite /I.inter /I.memi /=; apply /idP/idP; rewrite !zify; lia.
Qed.

Lemma mem_remove bytes i i' :
  ByteSet.mem (ByteSet.remove bytes i) i' -> ByteSet.mem bytes i' /\ disjoint_intervals i i'.
Proof.
  move=> /ByteSet.memP hsubset; split.
  + apply /ByteSet.memP => n /hsubset.
    by rewrite ByteSet.removeE => /andP [].
  rewrite /disjoint_intervals; apply /I.is_emptyP.
  move => n; apply /negP; rewrite interE.
  move=> /andP [hmem1 hmem2].
  by move: (hsubset _ hmem2); rewrite ByteSet.removeE hmem1 andbF.
Qed.

(* devrait-on remplacer les deux hypothèses par des wf_zone ? *)
Lemma disjoint_interval_of_zone z1 z2 :
  0 < z1.(z_len) -> 0 < z2.(z_len) ->
  disjoint_intervals (interval_of_zone z1) (interval_of_zone z2) =
  disjoint_zones z1 z2.
Proof.
  move=> hlen1 hlen2.
  rewrite /disjoint_intervals /interval_of_zone /disjoint_zones /I.is_empty /=.
  by apply /idP/idP; rewrite !Zcmp_le !zify; lia.
Qed.

Lemma eq_sub_region_val_same_region s2 sr ty sry ty' mem2 bytes v :
  wf_sub_region sr ty ->
  wf_sub_region sry ty' ->
  sr.(sr_region) = sry.(sr_region) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  eq_sub_region_val ty' (emem s2) sry bytes v ->
  eq_sub_region_val ty' mem2 sry (ByteSet.remove bytes (interval_of_zone sr.(sr_zone))) v.
Proof.
  move=> hwf hwfy hr hreadeq [hread hty'].
  split=> // off; rewrite memi_mem_U8 => /mem_remove [hmem hdisj] v1 hget.
  rewrite -(hread _ _ _ hget); last by rewrite memi_mem_U8.
  apply hreadeq.
  rewrite (sub_region_addr_offset (wsize_size U8)).
  have hwfy': wf_sub_region (sub_region_at_ofs sry (Some off) (wsize_size U8)) sword8.
  + change (wsize_size U8) with (size_of sword8).
    apply: (sub_region_at_ofs_wf hwfy).
    move=> _ [<-]; rewrite /= wsize8 -hty'.
    by have := get_val_byte_bound hget; lia.
  apply (disjoint_zones_disjoint_zrange hwf hwfy' hr).
  rewrite (disjoint_interval_of_zone (wf_zone_len_gt0 hwf)) // in hdisj.
  by apply (disjoint_zones_incl (zbetween_zone_sub_zone_at_ofs_0 hwf)
                                (zbetween_zone_sub_zone_at_ofs_0 hwfy')).
Qed.

(*
Lemma get_local_pos_sptr x ofs : get_local pmap x = Some (Pstkptr ofs) -> local_pos x = Some(ofs, sword Uptr).
Proof. by rewrite /local_pos => ->. Qed.

Lemma sptr_addr x ofs: 
  local_pos x = Some (ofs, sword Uptr) ->
  wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) = wunsigned rsp + ofs.
Proof.
  move=> h; assert (h1:= wfg_ofs wf_locals h).
  rewrite /mp_addr /wptr /=; apply wunsigned_add.
  move: (gt0_size_of (sword Uptr)) (@ge0_wunsigned Uptr rsp); lia.
Qed.

Lemma sptr_addr_bound x ofs:
  local_pos x = Some (ofs, sword Uptr) ->
  wunsigned rsp <= wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) /\
  wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) + wsize_size Uptr <= wunsigned rsp + stk_size.
Proof.
  move=> h; rewrite (sptr_addr h).
  assert (h1:= wfg_ofs wf_locals h); move: h1 => /=; lia.
Qed.
*)

Lemma sub_region_pk_valid rmap s sr pk :
  sub_region_pk pk = ok sr -> valid_pk rmap s sr pk.
Proof. by case: pk => // v ofs ws z [|//] [<-]. Qed.

Lemma sub_region_pk_wf x pk sr ws :
  get_local pmap x = Some pk ->
  x.(vtype) = sword ws ->
  sub_region_pk pk = ok sr ->
  wf_sub_region sr x.(vtype).
Proof.
  case: pk => // v ofs ws' z [|//] /wf_locals /= hget hty /= [<-].
  case: hget => *.
  by rewrite /sub_region_addr /sub_region_stack; split.
Qed.

Lemma sub_region_stkptr_wf y s ofs ws z f :
  wf_stkptr y s ofs ws z f ->
  wf_sub_region (sub_region_stkptr s ws z) sptr.
Proof. by case. Qed.

Lemma is_align_sub_region_stkptr x s ofs ws z f :
  wf_stkptr x s ofs ws z f ->
  is_align (sub_region_addr (sub_region_stkptr s ws z)) Uptr.
Proof.
  move=> hlocal.
  rewrite /sub_region_addr /=.
  (* TODO: could wfs_offset_align be is_align z.(z_ofs) U64 ?
     does it make sense ?
  *)
  apply: is_align_add hlocal.(wfs_offset_align).
  apply (is_align_m hlocal.(wfs_align_ptr)).
  rewrite -hlocal.(wfs_align).
  by apply (slot_align (sub_region_stkptr_wf hlocal).(wfr_slot)).
Qed.

Lemma get_bytes_map_setP rv r r' bm :
  get_bytes_map r (Mr.set rv r' bm) = if r' == r then bm else get_bytes_map r rv.
Proof. by rewrite /get_bytes_map Mr.setP; case: eqP. Qed.

Lemma get_bytes_setP bm x x' bytes :
  get_bytes x (Mvar.set bm x' bytes) = if x' == x then bytes else get_bytes x bm.
Proof. by rewrite /get_bytes Mvar.setP; case: eqP. Qed.

Lemma get_bytes_clear x i bm :
  get_bytes x (clear_bytes_map i bm) =
  ByteSet.remove (get_bytes x bm) i.
Proof.
  rewrite /clear_bytes_map /get_bytes.
  by rewrite Mvar.mapP; case: Mvar.get => //=; rewrite remove_empty.
Qed.

(* TODO: factorize set_sub_region and similar *)
Lemma get_var_bytes_set_pure_bytes rmap x sr ofs len r y :
  get_var_bytes (set_pure_bytes rmap x sr ofs len) r y =
    let bytes := get_var_bytes rmap r y in
    if sr.(sr_region) != r then
      bytes
    else
      let i := interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs len) in
      if x == y then
        if ofs is None then
          bytes
        else
          ByteSet.add i bytes
      else
        ByteSet.remove bytes i.
Proof.
  rewrite /set_pure_bytes /get_var_bytes /=.
  rewrite get_bytes_map_setP.
  case: eqP => [->|] //=.
  rewrite get_bytes_setP.
  by case: eqP => [->|] // _; rewrite get_bytes_clear.
Qed.

Lemma set_bytesP rmap x sr ofs len rv :
  set_bytes rmap x sr ofs len = ok rv ->
  sr.(sr_region).(r_writable) /\ rv = set_pure_bytes rmap x sr ofs len.
Proof. by rewrite /set_bytes; t_xrbindP=> _ /assertP. Qed.

Lemma set_sub_regionP rmap x sr ofs len rmap2 :
  set_sub_region rmap x sr ofs len = ok rmap2 ->
  sr.(sr_region).(r_writable) /\
  rmap2 = {| var_region := Mvar.set (var_region rmap) x sr;
             region_var := set_pure_bytes rmap x sr ofs len |}.
Proof. by rewrite /set_sub_region; t_xrbindP=> _ /set_bytesP [? ->] <-. Qed.

(*
Definition get_gvar_bytes rv r x :=
  if is_glob x then
    ByteSet.full (interval_of_zone {| z_ofs := 0; z_len := size_slot x.(gv) |})
  else get_var_bytes rv r x.(gv).
*)

Lemma check_gvalid_set_sub_region rmap x sr ofs len rmap2 y sry bytes :
  wf_sub_region sr x.(vtype) ->
  set_sub_region rmap x sr ofs len = ok rmap2 ->
  check_gvalid rmap2 y = Some (sry, bytes) ->
    [/\ ~ is_glob y, x = gv y, sr = sry &
         bytes = get_var_bytes rmap2 sr.(sr_region) x]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        exists bytes', check_gvalid rmap y = Some (sry, bytes') /\
          bytes =
            if sr.(sr_region) != sry.(sr_region) then bytes'
            else ByteSet.remove bytes' (interval_of_zone (sub_zone_at_ofs sr.(sr_zone) ofs len))].
(*               get_gvar_bytes (set_sub_region rmap x sr) sry.(sr_region) y]. *)
Proof.
  move=> hwf /set_sub_regionP [hw ->]; rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs' ws]|//] [<- <-].
    right; split => //.
    eexists; split; first by reflexivity.
    case: eqP => heqr //=.
    by rewrite -hwf.(wfr_writable) heqr (sub_region_glob_wf (wf_globals heq)).(wfr_writable) in hw.
  rewrite Mvar.setP; case: eqP.
  + by move=> -> [<- <-]; left; split.
  move=> hneq.
  case heq': Mvar.get => [sr'|//] [? <-]; subst sr'.
  right; split => //.
  eexists; split; first by reflexivity.
  rewrite get_var_bytes_set_pure_bytes.
  by move: hneq => /eqP /negPf ->.
Qed.

Definition between_at_ofs sr ty ofs ty2 p ws :=
  between (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty2)))
          (size_of (stype_at_ofs ofs ty2 ty))
          p ws.

(* This lemma is used for [set_sub_region] and [set_stack_ptr]. *)
Lemma mem_unchanged_write_slot m0 s1 s2 sr ty mem2 :
  wf_sub_region sr ty ->
  sr.(sr_region).(r_writable) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  mem_unchanged (emem s1) m0 (emem s2) ->
  mem_unchanged (emem s1) m0 mem2.
Proof.
  move=> hwf hwritable hreadeq hunch p hvalid1 hvalid2 hdisj.
  rewrite (hunch _ hvalid1 hvalid2 hdisj).
  symmetry; apply hreadeq.
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf)).
  apply (hdisj _ hwf.(wfr_slot)).
  by rewrite hwf.(wfr_writable).
Qed.

(*
Lemma disjoint_writable_is_constant_set_sub_region rmap m0 s1 s2 sr x ofs ty p ws w mem2 rmap2 :
  wf_sub_region sr x.(vtype) ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  between_at_ofs sr x.(vtype) ofs ty p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  disjoint_writable_is_constant (emem s1) m0 (emem s2) ->
  disjoint_writable_is_constant (emem s1) m0 mem2.
Proof.
  move=> hwf hofs hb hmem2 hset hunch p' hvalid1 hvalid2 hdisj.
  rewrite (hunch _ hvalid1 hvalid2 hdisj).
  symmetry; apply (Memory.writeP_neq hmem2).
  move: hset => /set_sub_regionP [hwritable _].
  have := hdisj _ hwf.(wfr_slot).
  rewrite hwf.(wfr_writable)=> /(_ hwritable).
  apply: disjoint_zrange_incl_l.
  apply: zbetween_trans hb.
  by apply (zbetween_sub_region_addr (sub_region_at_ofs_wf hwf hofs)).
Qed.*)

(* I tried to avoid proof duplication with this auxiliary lemma. But there is
   some duplication even in the proof of this lemma...
*)
Lemma valid_pk_set_pure_bytes rmap s2 x sr ofs ty mem2 y pk sry :
  wf_sub_region sr x.(vtype) ->
  ~ Sv.In x pmap.(vnew) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  wf_local y pk ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  valid_pk rmap s2 sry pk ->
  valid_pk (set_pure_bytes rmap x sr ofs (size_of ty)) (with_mem s2 mem2) sry pk.
Proof.
  move=> hwf hnin hreadeq hlocal hofs hpk.
  case: pk hlocal hofs hpk => //= s ofs' ws' z f hlocal hofs hpk.
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  have hwf2 := sub_region_stkptr_wf hlocal.
  rewrite /check_stack_ptr get_var_bytes_set_pure_bytes.
  case: eqP => heqr /=.
  + case: eqP => heq2.
    + by have := hlocal.(wfs_new); congruence.
    move=> /mem_remove [] /hpk <-.
    rewrite (disjoint_interval_of_zone (wf_zone_len_gt0 hwf')) // => hdisj.
    apply hreadeq.
    apply (disjoint_zones_disjoint_zrange hwf' hwf2 heqr).
    apply: disjoint_zones_incl_l hdisj.
    by apply (zbetween_zone_sub_zone_at_ofs_0 hwf').
  move=> /hpk <-.
  apply hreadeq.
  apply (disjoint_zrange_incl (zbetween_sub_region_addr hwf') (zbetween_sub_region_addr hwf2)).
  apply disjoint_zrange_sym.
  apply (disjoint_writable hwf2.(wfr_slot) hwf.(wfr_slot)); last by rewrite hwf2.(wfr_writable).
  by move=> /(wf_region_slot_inj hwf2 hwf); congruence.
Qed.

Lemma wfr_PTR_set_sub_region (rmap : region_map) s2 x pk sr ofs ty mem2 rmap2 :
  get_local pmap x = Some pk ->
  wf_sub_region sr x.(vtype) ->
  valid_pk rmap s2 sr pk ->
  (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  wfr_PTR rmap s2 ->
  wfr_PTR rmap2 (with_mem s2 mem2).
Proof.
  move=> hlx hwf hpk hreadeq hofs /set_sub_regionP [_ ->] hptr y sry.
  have /wf_vnew hnnew := hlx.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists pk; split=> //.
    by apply (valid_pk_set_pure_bytes hwf hnnew hreadeq (wf_locals hlx) hofs hpk).
  move=> _ /hptr {pk hlx hpk} [pk [hly hpk]].
  exists pk; split=> //.
  by apply (valid_pk_set_pure_bytes hwf hnnew hreadeq (wf_locals hly) hofs hpk).
Qed.

Lemma pto_val_pof_val v t :
  pof_val (type_of_val v) v = ok t ->
  pto_val t = v.
Proof.
  case: v t => /=.
  + by move=> ?? [->].
  + by move=> ?? [->].
  + by move=> len a ?; rewrite WArray.castK => -[<-].
  + by move=> ws w pw; rewrite sumbool_of_boolET => -[<-].
  by move=> [].
Qed.

Lemma check_gvalid_lvar rmap (x : var_i) sr :
  Mvar.get rmap.(var_region) x = Some sr ->
  check_gvalid rmap (mk_lvar x) = Some (sr, get_var_bytes rmap sr.(sr_region) x).
Proof. by rewrite /check_gvalid /= => ->. Qed.

Lemma wfr_VAL_set_sub_region rmap s1 s2 sr x ofs ty mem2 (rmap2 : region_map) v :
  wf_rmap rmap s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  eq_sub_region_val x.(vtype) mem2 sr (get_var_bytes rmap2 sr.(sr_region) x) v ->
  wfr_VAL rmap2 (with_vm s1 (evm s1).[x <- pof_val (vtype x) v]) (with_mem s2 mem2).
Proof.
  move=> hwfr hwf hofs hreadeq hset hval y sry bytesy vy.
  move=> /(check_gvalid_set_sub_region hwf hset) [].
  + move=> [? ? <- ->]; subst x.
    have [_ hty] := hval.
    rewrite get_gvar_eq //.
    apply on_vuP => //; rewrite -hty.
    by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty.
  move=> [? [bytes [hgvalid ->]]].
  rewrite get_gvar_neq => //; move=> /(wfr_val hgvalid).
  assert (hwfy := check_gvalid_wf wfr_wf hgvalid).
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  case: eqP => heqr /=.
  + apply (eq_sub_region_val_same_region hwf' hwfy heqr hreadeq).
  apply: (eq_sub_region_val_disjoint_regions hwf' hwfy heqr _ hreadeq).
  by case /set_sub_regionP : hset.
Qed.

(* This lemma is used for [set_sub_region] and [set_stack_ptr]. *)
Lemma eq_mem_source_write_slot rmap m0 s1 s2 sr ty mem2:
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr ty ->
  (forall p ws,
    disjoint_zrange (sub_region_addr sr) (size_of ty) p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  eq_mem_source (emem s1) mem2.
Proof.
  move=> hvs hwf hreadeq p hvp.
  rewrite (vs_eq_mem hvp).
  symmetry; apply hreadeq.
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf)).
  by apply (vs_disjoint hwf.(wfr_slot) hvp).
Qed.

(*
Lemma eq_not_mod_rset_word rmap m0 s1 s2 x mp p ws w mem2:
  valid_state rmap m0 s1 s2 ->  
  Mvar.get (var_region rmap) x = Some mp ->
  mp_s mp = MSstack ->
  between (mp_addr mp) (size_of (vtype x)) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  eq_not_mod m0 (emem s2) -> 
  eq_not_mod m0 mem2. 
Proof.
  move=> hvs hgx hms hb hw heg p1 ws1 hvp.
  rewrite (heg _ _ hvp) //; symmetry; apply: (Memory.writeP_neq hw).
  assert (hmp := wfr_valid_mp hgx).
  case: (hmp) => x' [] /size_of_le hle; rewrite hms /= => hx.
  split.
  + by apply (is_align_no_overflow (Memory.valid_align (write_mem_validw hw))).
  + by apply: is_align_no_overflow; apply is_align8.
  move: hb; rewrite /between !zify.
  have:= hvp _ _ _ (get_local_pos hx).
  rewrite wunsigned_add; last by have := @ge0_wunsigned _ rsp; lia.
  rewrite (valid_mp_addr hmp) /wptr hms wsize8 /=; lia.
Qed.
*)

Lemma set_wordP rmap x sr ws rmap2 :
  wf_sub_region sr x.(vtype) ->
  set_word rmap x sr ws = ok rmap2 ->
    is_align (sub_region_addr sr) ws /\
    set_sub_region rmap x sr (Some 0) (size_slot x) = ok rmap2.
Proof.
  by rewrite /set_word; t_xrbindP=> hwf _ /(check_alignP hwf).
Qed.

(* TODO: better name? *)
Lemma wfr_WF_set rmap x sr rmap2 :
  wfr_WF rmap ->
  wf_sub_region sr x.(vtype) ->
  rmap2.(var_region) = Mvar.set rmap.(var_region) x sr ->
  wfr_WF rmap2.
Proof.
  move=> hwsrf hwfsr hrmap2 y sry.
  rewrite hrmap2 Mvar.setP.
  by case: eqP; [congruence|auto].
Qed.

(* We show that, under the right hypotheses, [set_sub_region] preserves
   the [valid_state] invariant.
   This lemma is used both for words and arrays.
*)
Lemma valid_state_set_sub_region rmap m0 s1 s2 sr x pk ofs ty mem2 v (rmap2 : region_map) :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some pk ->
  valid_pk rmap.(region_var) s2 sr pk ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  (forall p ws, validw mem2 p ws = validw (emem s2) p ws) ->
 (forall p ws,
    disjoint_zrange (sub_region_addr (sub_region_at_ofs sr ofs (size_of ty)))
                    (size_of (stype_at_ofs ofs ty x.(vtype)))
                    p (wsize_size ws) ->
    read mem2 p ws = read (emem s2) p ws) ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  eq_sub_region_val x.(vtype) mem2 sr (get_var_bytes rmap2 sr.(sr_region) x) v ->
  valid_state rmap2 m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) (with_mem s2 mem2).
Proof.
  move=> hvs hwf hlx hpk hofs hvalideq hreadeq hset heqval.
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor => //=.
  + by move=> ??; rewrite hvalideq; apply hvalid.
  + by move=> ??; rewrite hvalideq; apply hincl.
  + case /set_sub_regionP : hset => hwritable _.
    by apply (mem_unchanged_write_slot hwf' hwritable hreadeq hunch).
  + move=> y hget; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  + case: (hwfr) => hwfsr hval hptr; split.
    + apply (wfr_WF_set hwfsr hwf).
      by have [_ ->] := set_sub_regionP hset.
    + by apply (wfr_VAL_set_sub_region hwfr hwf hofs hreadeq hset heqval).
    by apply (wfr_PTR_set_sub_region hlx hwf hpk hreadeq hofs hset hptr).
  by apply (eq_mem_source_write_slot hvs hwf' hreadeq).
Qed.

Lemma disjoint_range_valid_not_valid_U8 m p1 ws1 p2 :
  validw m p1 ws1 ->
  ~ validw m p2 U8 ->
  disjoint_range p1 ws1 p2 U8.
Proof.
  move=> /validwP [hal1 hval1] hnval.
  split.
  + by apply is_align_no_overflow.
  + by apply is_align_no_overflow; apply is_align8.
  rewrite wsize8.
  case: (Z_le_gt_dec (wunsigned p1 + wsize_size ws1) (wunsigned p2)); first by left.
  case: (Z_le_gt_dec (wunsigned p2 + 1) (wunsigned p1)); first by right.
  move=> hgt1 hgt2.
  case: hnval.
  apply /validwP; split.
  + by apply is_align8.
  move=> k; rewrite wsize8 => hk; have ->: k = 0 by lia.
  rewrite add_0.
  have ->: p2 = (p1 + wrepr _ (wunsigned p2 - wunsigned p1))%R.
  + by rewrite wrepr_sub !wrepr_unsigned; ssrring.ssring. (* proof from memory_model *)
  by apply hval1; lia.
Qed.

Lemma set_arr_wordP rmap m0 s1 s2 x ofs ws rmap2 :
  valid_state rmap m0 s1 s2 ->
  set_arr_word rmap x ofs ws = ok rmap2 ->
  exists sr, [/\
    Mvar.get rmap.(var_region) x = Some sr,
    is_align (sub_region_addr sr) ws &
    set_sub_region rmap x sr ofs (wsize_size ws) = ok rmap2].
Proof.
  move=> hvs.
  rewrite /set_arr_word; t_xrbindP=> sr /get_sub_regionP hget.
  have /wfr_wf hwf := hget.
  move=> _ /(check_alignP hwf) halign.
  by exists sr; split.
Qed.

Lemma zbetween_zone_zbetween sr1 sr2 ty1 ty2 :
  wf_sub_region sr1 ty1 ->
  wf_sub_region sr2 ty2 ->
  sr_region sr1 = sr_region sr2 ->
  zbetween_zone (sub_zone_at_ofs (sr_zone sr1) (Some 0) (size_of ty1))
                (sub_zone_at_ofs (sr_zone sr2) (Some 0) (size_of ty2)) ->
  zbetween (sub_region_addr sr1) (size_of ty1) (sub_region_addr sr2) (size_of ty2).
Proof.
  move=> hwf1 hwf2 heq.
  rewrite /zbetween_zone /zbetween !zify /=.
  rewrite (wunsigned_sub_region_addr hwf1).
  rewrite (wunsigned_sub_region_addr hwf2).
  rewrite heq.
  by lia.
Qed.

Lemma zbetween_sub_region_at_ofs sr ty ofs ws :
  wf_sub_region sr ty ->
  (∀ zofs : Z, ofs = Some zofs → 0 <= zofs ∧ zofs + wsize_size ws <= size_of ty) ->
  zbetween (sub_region_addr sr) (size_of ty)
           (sub_region_addr (sub_region_at_ofs sr ofs (wsize_size ws))) (size_of (stype_at_ofs ofs (sword ws) ty)).
Proof.
  move=> hwf hofs.
  change (wsize_size ws) with (size_of (sword ws)) in hofs.
  have hwf' := sub_region_at_ofs_wf hwf hofs.
  rewrite /zbetween !zify.
  rewrite (wunsigned_sub_region_addr hwf).
  rewrite (wunsigned_sub_region_addr hwf').
  case: ofs hofs {hwf'} => [ofs|] /=.
  + by move=> /(_ _ refl_equal); lia.
  by lia.
Qed.

Lemma zbetween_sub_region_at_ofs_option sr ofs ws i ty :
  wf_sub_region sr ty ->
  0 <= i /\ i + wsize_size ws <= size_of ty ->
  (ofs <> None -> ofs = Some i) ->
  zbetween (sub_region_addr (sub_region_at_ofs sr ofs (wsize_size ws))) (size_of (stype_at_ofs ofs (sword ws) ty))
           (sub_region_addr sr + wrepr _ i) (wsize_size ws).
Proof.
  move=> hwf hi.
  rewrite (sub_region_addr_offset (wsize_size ws)).
  case: ofs => [ofs|] /=.
  + by move=> /(_ ltac:(discriminate)) [->]; apply zbetween_refl.
  move=> _; rewrite sub_region_at_ofs_None.
  apply: (zbetween_sub_region_at_ofs hwf).
  by move=> _ [<-].
Qed.

(* TODO: move? *)
Lemma subtype_of_val_to_pword ws v (w : pword ws) :
  subtype (sword ws) (type_of_val v) ->
  to_pword ws v = ok w ->
  exists ws' (w' : word ws'),
    [/\ (ws <= ws')%CMP, w = pword_of_word (zero_extend ws w') & v = Vword w'].
Proof.
  move=> /subtypeEl [] ws' [] hty /dup[] hle.
  rewrite cmp_le_eq_lt => /orP [].
  + rewrite -cmp_nle_lt => /negPf hlt.
    move=> /to_pwordI [] ws'' [] w' [] ?; subst v.
    case: hty => ?; subst ws''.
    rewrite sumbool_of_boolEF => ->.
    by exists ws', w'.
  move=> /eqP ?; subst ws' => hto.
  have [w' [hw hv]] := (type_of_val_to_pword hty hto).
  exists ws, w'; split=> //.
  by rewrite zero_extend_u.
Qed.

Lemma to_pword_u ws (w : word ws) :
  to_pword ws (Vword w) = ok (pword_of_word w).
Proof. by rewrite /= sumbool_of_boolET. Qed.

(* A version of [write_read8] easier to use. *)
Lemma write_read8_no_overflow mem1 mem2 p ofs ws (w: word ws) :
  0 <= ofs /\ ofs + wsize_size ws <= wbase Uptr ->
  write mem1 (p + wrepr _ ofs)%R w = ok mem2 ->
  forall k, 0 <= k < wbase Uptr ->
    read mem2 (p + wrepr _ k)%R U8 =
      let i := k - ofs in
      if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 w i)
      else read mem1 (p + wrepr _ k)%R U8.
Proof.
  move=> hofs hmem2 k hk.
  rewrite (write_read8 hmem2).
  rewrite subE {1}(GRing.addrC p) GRing.addrKA /=.
  rewrite wunsigned_sub_if.
  have hws := wsize_size_pos ws.
  rewrite !wunsigned_repr_small //; last by lia.
  case: (ZleP ofs k) => [//|hlt].
  case: (ZleP 0 (k - ofs)) => [|_]; first by lia.
  case: ZltP => [|_]; first by lia.
  by rewrite andFb andbF.
Qed.

(* Hypotheses are more restrictive but are those available in the proofs. *)
Lemma write_read8_sub_region mem1 mem2 sr ty ofs ws (w: word ws) :
  wf_sub_region sr ty ->
  0 <= ofs /\ ofs + wsize_size ws <= size_of ty ->
  write mem1 (sub_region_addr sr + wrepr _ ofs)%R w = ok mem2 ->
  forall k, 0 <= k < size_of ty ->
    read mem2 (sub_region_addr sr + wrepr _ k)%R U8 =
      let i := k - ofs in
      if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 w i)
      else read mem1 (sub_region_addr sr + wrepr _ k)%R U8.
Proof.
  move=> hwf hofs hmem2 k hk.
  have := no_overflow_sub_region_addr hwf; rewrite /no_overflow !zify => hover.
  have ? := ge0_wunsigned (sub_region_addr sr).
  by apply: (write_read8_no_overflow _ hmem2); lia.
Qed.

(* TODO : disjoint_intervals (interval_of_zone _ ) = disjoint_zones z1 z2
          et disjoint_zones -> disjoint_zrange avec même base *)
Lemma alloc_lvalP rmap r1 r2 v ty m0 (s1 s2: estate) :
  alloc_lval pmap rmap r1 ty = ok r2 -> 
  valid_state rmap m0 s1 s2 -> 
  type_of_val v = ty ->
  forall s1', write_lval gd r1 v s1 = ok s1' ->
  exists s2', write_lval [::] r2.2 v s2 = ok s2' /\ valid_state r2.1 m0 s1' s2'.
Proof.
  move=> ha hvs ?; subst ty.
  case: r1 ha => //; rewrite /alloc_lval.
  (* Lnone *)
  + move=> vi ty1 [<-] /= s1' /write_noneP [->] h; exists s2; split => //.
    by rewrite /write_none; case: h => [ [? ->]| [-> ->]].

  (* Lvar *)
  + move=> x.
    case hlx: get_local => [pk | ]; last first.
    + t_xrbindP=> _ /check_diffP hnnew <- s1' /=.
      rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
      by apply: set_varP hvm1=> [v' hv <- | hb hv <-]; rewrite /write_var /set_var hv /= ?hb /=;
        eexists;(split;first by reflexivity); apply valid_state_set_var.
    case heq: is_word_type => [ws | //]; move /is_word_typeP : heq => hty.
    case htyv: subtype => //; rewrite /= /write_var.
    t_xrbindP => -[xi ei] ha sr hsr rmap2 hsetw <- /= s1' vm1' hvm1' ?; subst s1' => /=.
    have he1 : sem_pexpr [::] s2 0 >>= to_int = ok 0 by done.
    have hpk := sub_region_pk_valid rmap s2 hsr.
    have [wx [wi [-> -> /= <-]]]:= check_mk_addr_ptr hvs he1 (wf_locals hlx) hpk ha.
    move: hvm1'; apply set_varP; last by rewrite {1}hty.
    move=> {ha}; case: x hty hlx hsetw => -[xty xn] xii /= ->.
    set x := {| vtype := sword ws; vname := xn |} => hlx hsetw /= w hto <-.
    have [ws' [w' [hle ??]]] := subtype_of_val_to_pword htyv hto; subst w v.
    rewrite /= /truncate_word hle /=.
    have hwf := sub_region_pk_wf hlx refl_equal hsr.
    have hvp: validw (emem s2) (sub_region_addr sr + wrepr _ 0)%R ws.
    + rewrite wrepr0 GRing.addr0.
      have [halign _] := set_wordP hwf hsetw.
      by apply (validw_sub_region_addr hvs hwf halign).
    have /writeV -/(_ (zero_extend ws w')) [mem2 hmem2] := hvp.
    rewrite hmem2 /=; eexists;split;first by reflexivity.
    (* valid_state update word *)
    have [_ hset] := set_wordP hwf hsetw.
    rewrite -to_pword_u.
    have hofs: 0 <= 0 /\ size_of (sword ws) <= wsize_size ws by rewrite /=; lia.
    have hofs' := ofs_bound_option hofs (fun _ => refl_equal).
    apply: (valid_state_set_sub_region hvs hwf hlx hpk hofs' _ _ hset (v:=Vword (zero_extend ws w'))).
    + by move=> ??; apply (write_validw_eq hmem2).
    + move=> p ws''.
      rewrite -sub_region_addr_offset.
      by apply (writeP_neq hmem2).
    split => //.
    move=> off hmem w hget.
    have /= hoff := get_val_byte_bound hget.
    rewrite (write_read8_sub_region hwf hofs hmem2 hoff) Z.sub_0_r /=.
    move: (hoff); rewrite -!zify => ->.
    by rewrite -(get_val_byte_word _ hoff).

  (* Lmem *)
  + move=> ws x e1 /=; t_xrbindP => _ /check_varP hx _ /check_diffP hnnew e1' /(alloc_eP hvs) he1 <-.
    move=> s1' xp ? hgx hxp w1 v1 /he1 he1' hv1 w hvw mem1 hmem1 <- /=.
    have := get_var_kindP hvs hx hnnew; rewrite /get_gvar /= => /(_ _ hgx) -> /=.
    rewrite he1' hxp /= hv1 /= hvw /=.
    have hvp1 := write_validw hmem1.
    have /valid_incl_word hvp2 := hvp1.
    have /writeV -/(_ w) [mem2 hmem2] := hvp2.
    rewrite hmem2 /=; eexists;split;first reflexivity.
    (* valid_state update mem *)
    case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
    constructor => //=.
    + move=> ??; rewrite (write_validw_eq hmem2); apply hvalid.
    + by move=> ???; rewrite (write_validw_eq hmem1); apply hdisj.
    + move=> ?; rewrite (write_validw_eq hmem1) (write_validw_eq hmem2); apply hincl.
    + move=> p hvalid2; rewrite (write_validw_eq hmem1) => hvalid3 hdisj2.
      rewrite (hunch p hvalid2 hvalid3 hdisj2).
      symmetry; apply (writeP_neq hmem2).
      by apply (disjoint_range_valid_not_valid_U8 hvp1 hvalid3).
    + case: (hwfr) => hwfsr hval hptr; split=> //.
      + move=> y sry bytes vy hgvalid hgy.
        assert (hwfy := check_gvalid_wf hwfsr hgvalid).
        have hreadeq := writeP_neq hmem2.
        apply: (eq_sub_region_val_disjoint_zrange hreadeq _ (hval _ _ _ _ hgvalid hgy)).
        apply disjoint_zrange_sym.
        apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwfy)).
        by apply: disjoint_source_word hwfy.(wfr_slot) hvp1.
      move=> y sry hgy.
      have [pk [hgpk hvpk]] := hptr _ _ hgy; exists pk; split => //.
      case: pk hgpk hvpk => //= s ofs ws' z f hgpk hread /hread <-.
      apply: (writeP_neq hmem2).
      assert (hwf' := sub_region_stkptr_wf (wf_locals hgpk)).
      apply disjoint_zrange_sym.
      apply: (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf')).
      by apply: disjoint_source_word hwf'.(wfr_slot) hvp1.
    + move=> p; rewrite (write_validw_eq hmem1) => /validwP [_ hv].
      apply: read_write_any_mem hmem1 hmem2.
      by move=> k hk; apply heqmem; apply hv.
      (* TODO: since we are using only U8, read_write_any_mem could be simpler *)

  (* Laset *)
  move=> aa ws x e1 /=; t_xrbindP => e1' /(alloc_eP hvs) he1.
  move=> hr2 s1'; apply on_arr_varP => n t hty hxt.
  t_xrbindP => i1 v1 /he1 he1' hi1 w hvw t' htt' vm1 hvm1 ?; subst s1'.
  case hlx: get_local hr2 => [pk | ]; last first.
  + t_xrbindP=> _ /check_diffP hnnew <-.
    have /get_var_kindP -/(_ _ hnnew hxt) : get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    rewrite /get_gvar /= => hxt2.
    rewrite he1' /= hi1 hxt2 /= hvw /= htt' /=.
    apply: set_varP hvm1=> [v' hv <- | ]; last by rewrite {1} hty.
    rewrite /set_var hv /=.
    by eexists;(split;first by reflexivity); apply valid_state_set_var.
  t_xrbindP => rmap2 /set_arr_wordP [sr [hget hal hset]] [xi ei] ha <- /=.
  have {he1} he1 : sem_pexpr [::] s2 e1' >>= to_int = ok i1 by rewrite he1'.
  have /wfr_ptr [pk' [hlx' hpk]] := hget.
  have hgvalid := check_gvalid_lvar hget.
  move: hlx'; rewrite hlx => -[?]; subst pk'.
  have [wx [wi [-> -> /= <-]]]:= check_mk_addr_ptr hvs he1 (wf_locals hlx) hpk ha.
  move: hvm1; apply set_varP; last by rewrite {1}hty.
  move=> {ha}; case: x hty hlx hxt hget hset hgvalid => -[xty xn] xii /= ->.
  set x := {| vtype := sarr n; vname := xn |} => hlx hxt hget hset hgvalid /= ti <- ?; subst vm1.
  rewrite hvw /=.
  have /wfr_wf hwf := hget.
  have [hge0 hlen haa] := WArray.set_bound htt'.
  have hvp: validw (emem s2) (sub_region_addr sr + wrepr _ (i1 * mk_scale aa ws))%R ws.
  + apply (validw_sub_region_at_ofs _ hwf (conj hge0 hlen)).
    apply is_align_add => //.
    by rewrite WArray.arr_is_align.
  have /writeV -/(_ w) [mem2 hmem2] := hvp.
  rewrite hmem2 /=; eexists;split;first by reflexivity.
  (* valid_state update array *)
  have hofs: 0 <= i1 * mk_scale aa ws /\ i1 * mk_scale aa ws + size_of (sword ws) <= size_slot x.
  + done.
  have hofs' := ofs_bound_option hofs (mk_ofsiP he1).
  have hvalideq := write_validw_eq hmem2.
  apply: (valid_state_set_sub_region hvs hwf hlx hpk hofs' hvalideq _ hset (v:=Varr t')).
  + move=> p ws' hdisj.
    apply (writeP_neq hmem2).
    apply: disjoint_zrange_incl_l hdisj.
    by apply: (zbetween_sub_region_at_ofs_option hwf _ (mk_ofsiP he1)).
  split=> //.
  move=> off hmem w0 hget'.
  have /= hoff := get_val_byte_bound hget'.
  rewrite (write_read8_sub_region hwf hofs hmem2 hoff) /=.
  move: hget'; rewrite /= (write_read8 htt') WArray.subE /=.
  case: ifP => // hle.
  assert (hval := wfr_val hgvalid hxt).
  case: hval => hread _.
  apply hread.
  move: hset hmem => /set_sub_regionP [_ ->] /=.
  rewrite get_var_bytes_set_pure_bytes !eq_refl /=.
  case heq: mk_ofsi => [ofs'|//].
  have := mk_ofsiP he1 (aa:=aa) (sz:=ws).
  rewrite heq => /(_ ltac:(discriminate)) [->].
  rewrite ByteSet.addE => /orP [|//].
  by move /andP : hle; rewrite /I.memi /= !zify; lia.
Qed.

Lemma alloc_lvalsP rmap r1 r2 vs ty m0 (s1 s2: estate) :
  alloc_lvals pmap rmap r1 ty = ok r2 -> 
  valid_state rmap m0 s1 s2 -> 
  seq.map type_of_val vs = ty -> 
  forall s1', write_lvals gd s1 r1 vs = ok s1' ->
  exists s2', write_lvals [::] s2 r2.2 vs = ok s2' /\ valid_state r2.1 m0 s1' s2'.
Proof.
  elim: r1 r2 rmap ty vs s1 s2=> //= [|a l IH] r2 rmap [ | ty tys] // [ | v vs] //.
  + move=> s1 s2 [<-] Hvalid _ s1' [] <-; by exists s2; split.
  move=> vs's1 s2; t_xrbindP => -[a' r3] ha [l' r4] /IH hrec <-.
  move=> Hvalid [] hty htys s1' s1'' ha1 hl1.
  have [s2' [hs2' vs2']]:= alloc_lvalP ha Hvalid hty ha1.
  have [s2'' [hs2'' vs2'']]:= hrec _ _ _ vs2' htys _ hl1.
  by exists s2''; split => //=; rewrite hs2'.
Qed.



(*Hypothesis P

Let P' : sprog := 
    {| p_globs := [::];
       p_funcs := SP;
       p_extra := {|
         sp_rip := gm.(stack_alloc.rip); 
         sp_globs := data; 
         sp_stk_id := nrsp |}
    |}. *)

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].

(*
Lemma alloc_assgnP s1 s2 x tag ty e v v' ii1 ii2 i2 sm1 sm2:
  sem_pexpr gd s1 e = ok v -> 
  truncate_val ty v = ok v' -> 
  write_lval gd x v' s1 = ok s2 -> 
  Let ir := alloc_assgn nrsp gm sm1 ii1 x tag ty e in ok (ir.1, MkI ii1 ir.2) = ok (sm2, MkI ii2 i2) ->
  forall s1', valid sm1 s1 s1' → 
   ∃ s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' ∧ valid sm2 s2 s2'.
Proof.
  move=> hv htr Hw; rewrite /alloc_assgn.
  t_xrbindP => -[sm i'] e'; apply: add_iinfoP => he [sm' x'].
  apply: add_iinfoP => ha /= [?] ???? s1' hs1; subst i' sm sm' ii1 i2.
  have [v1 [He' Uvv1]] := alloc_eP he hs1 hv.
  have [v1' htr' Uvv1']:= truncate_value_uincl Uvv1 htr.
  have hty := truncate_val_has_type htr.
  have [s2' [Hw' Hs2']] := alloc_lvalP ha hs1 hty Uvv1' Hw.
  by exists s2'; split=> //;apply: Eassgn;eauto.
Qed.

  Lemma is_arr_typeP ty : is_arr_type ty -> exists n, ty = sarr n.
  Proof. case ty => //;eauto. Qed.

  Lemma is_varP e y: is_var e = Some y -> e = Pvar y.
  Proof. by case e => // ? [->]. Qed.

  Lemma find_gvar_set sm x ap z: 
    find_gvar gm (Mvar.set sm x ap) z = 
      if is_lvar z && (x == gv z) then Some (mp_of_ap ap) else find_gvar gm sm z.
  Proof.
    by rewrite /find_gvar; case: ifP => //= ?; rewrite Mvar.setP; case: ifP.
  Qed.
*)

Lemma is_sarrP ty : reflect (exists n, ty = sarr n) (is_sarr ty).
Proof.
  case: ty => /= [||n|ws]; constructor; try by move => -[].
  by exists n.
Qed.
(*
Lemma get_set_region rmap x mp y :
  Mvar.get (var_region (set rmap x mp)) y = 
  if x == y then Some mp else Mvar.get (var_region rmap) y.
Proof. rewrite /set /= Mvar.setP; case: ifPn => // hne. Qed.

Lemma set_VALID rmap x mp: 
  valid_mp mp (vtype x) -> wfr_VALID rmap -> wfr_VALID (set rmap x mp).    
Proof.
  by move=> hv hV y mpy; rewrite get_set_region; case: eqP => [<- [<-]| _ /hV ].
Qed.

Lemma check_gvalid_set rmap x mp y: 
  check_gvalid (set rmap x mp) y = 
    if (x == (gv y)) && ~~is_glob y then Some mp 
    else check_gvalid rmap y.
Proof.
  rewrite /check_gvalid; case: ifPn => ? /=; first by rewrite andbF.
  rewrite andbT /check_valid get_set_region; case: eqP => [-> | hne].
  + by rewrite /set /= Mmp.setP_eq SvP.add_mem_1.
  case: Mvar.get => // mpy.
  rewrite /set /= Mmp.setP; case: eqP => // <-.
  by rewrite SvD.F.add_neq_b //; case: Mmp.get.
Qed.

Lemma set_VAL rmap x mp v s s': 
  eq_mp_val (vtype x) (emem s') mp (pto_val v) ->
  wfr_VAL rmap s s' -> 
  wfr_VAL (set rmap x mp) (with_vm s (evm s).[x <- ok v]) s'.
Proof.
  move=> hv hV y mpy vy; rewrite check_gvalid_set.
  case: ifPn => [ /andP[]/eqP heq /negP ? [<-]| ].
  + by subst x; rewrite get_gvar_eq /= => [[<-]| ].
  move=> h /hV hc;rewrite get_gvar_neq => [/hc // |/negP hn ].
  by move: h;rewrite hn andbT => /eqP. 
Qed.

Lemma type_of_get_var x vm v: get_var vm x = ok v → subtype (type_of_val v) (vtype x).
Proof.
  rewrite /get_var; apply on_vuP => // v' _ <-; apply subtype_type_of_val.
Qed.

Lemma type_of_get_gvar x gd vm v: get_gvar gd vm x = ok v → subtype (type_of_val v) (vtype (gv x)).
Proof.
  by rewrite /get_gvar; case: ifPn => [ ? /type_of_get_var | ? /type_of_get_global ->].
Qed.
*)
Definition lea_ptr' y ptr ofs := 
  add (Pvar (mk_lvar (with_var y ptr))) (cast_const ofs).
(*
Lemma get_addrP s1 s1' rmap1 rmap2 i2 x dx y:
  valid_state rmap1 m0 s1 s1' ->
  get_addr pmap rmap1 x dx y = ok (rmap2, i2) ->
  exists mp, 
    [/\ check_gvalid rmap1 y = Some mp,
        rmap2 = set rmap1 x mp &
        forall s2', write_lval [::] dx (Vword (mp_addr mp)) s1' = ok s2' ->
                     sem_i P' rip s1' i2 s2'].
Proof.
  move=> hvs; rewrite /get_addr /check_gvalid.   
  case: ifPn => hglob.             
  + t_xrbindP => ofs /get_globalP -> <- <- /=.
    exists {| mp_s := MSglob; mp_ofs := ofs |}.
    split => //= s2' hs; constructor.
    by rewrite /sem_sopn /= P'_globs /get_gvar /= vs_rip /= /sem_sop2 /= !zero_extend_u hs.
  case heq: get_local => [pk | //].         
  rewrite /set_move; t_xrbindP => rmap2' mp hva <- <- <-; rewrite hva.
  case /check_validP : hva => hgmp _.
  assert (h := wfr_ptr hgmp); case: h => pk' [];rewrite heq => -[?] hvp {heq}; subst pk'.
  exists mp; split => // s2' hs .
  case: pk hvp => /= [ofs | p | ofs] h.
  + subst mp; constructor.
    by rewrite /sem_sopn /= P'_globs /get_gvar /= vs_rsp /= /sem_sop2 /= !zero_extend_u hs.
  + by constructor; rewrite /sem_sopn /= P'_globs /get_gvar /= h /= !zero_extend_u hs.
  by constructor; rewrite /sem_sopn /= P'_globs vs_rsp /= !zero_extend_u h /= !zero_extend_u hs.
Qed.
*)
(*
get_ofs_sub aa ws e ofs :
  get_ofs_sub aa ws e = ok ofs ->
  mk_ofsiP *)

Local Opaque arr_size.

(* TODO: move to WArray *)
Lemma get_sub_bound lena aa ws len (a:WArray.array lena) p a2 :
  WArray.get_sub aa ws len a p = ok a2 ->
  0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= lena.
Proof. by rewrite /WArray.get_sub; case: ifP => //; rewrite !zify. Qed.

Lemma get_ofs_subP gd s i aa ws e ofs :
  sem_pexpr gd s e >>= to_int = ok i ->
  get_ofs_sub aa ws e = ok ofs ->
  ofs = i * mk_scale aa ws.
Proof.
  move=> he; rewrite /get_ofs_sub.
  case heq: mk_ofsi => [ofs'|//] [<-].
  have := mk_ofsiP he (aa:=aa) (sz:=ws).
  by rewrite heq; move=> /(_ ltac:(discriminate)) [->].
Qed.

Lemma get_var_bytes_set_move_bytes rmap x sr r y :
  get_var_bytes (set_move_bytes rmap x sr) r y =
    let bytes := get_var_bytes rmap r y in
    if sr_region sr != r then
      bytes
    else
      if x == y then
        ByteSet.add (interval_of_zone sr.(sr_zone)) bytes
      else bytes.
Proof.
  rewrite /set_move_bytes /get_var_bytes get_bytes_map_setP.
  case: eqP => //= <-.
  rewrite get_bytes_setP.
  by case: eqP => //= <-.
Qed.

Lemma check_gvalid_set_move rmap x sr y sry bytes :
  check_gvalid (set_move rmap x sr) y = Some (sry, bytes) ->
    [/\ ~ is_glob y, x = gv y, sr = sry &
        bytes = get_var_bytes (set_move_bytes rmap x sr) sr.(sr_region) x]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        check_gvalid rmap y = Some (sry, bytes)].
Proof.
  rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs ws]|//] [<- <-].
    by right; split.
  rewrite Mvar.setP; case: eqP.
  + by move=> -> [<- <-]; left; split.
  move=> hneq.
  case heq': Mvar.get => [sr'|//] [? <-]; subst sr'.
  right; split => //.
  rewrite get_var_bytes_set_move_bytes.
  case: eqP => [_|//].
  by move: hneq=> /eqP /negPf ->.
Qed.

Lemma set_arr_subP rmap x ofs len sr_from rmap2 :
  set_arr_sub rmap x ofs len sr_from = ok rmap2 ->
  exists sr, [/\
    Mvar.get rmap.(var_region) x = Some sr,
    sub_region_at_ofs sr (Some ofs) len = sr_from &
    set_move_sub rmap x (sub_region_at_ofs sr (Some ofs) len) = rmap2].
Proof.
  rewrite /set_arr_sub.
  t_xrbindP=> sr /get_sub_regionP -> _ /assertP /eqP heqsub hmove.
  by exists sr.
Qed.

Lemma check_gvalid_set_move_sub rmap x sr y sry bytes :
  check_gvalid (set_move_sub rmap x sr) y = Some (sry, bytes) ->
    ([/\ ~ is_glob y, x = gv y, Mvar.get rmap.(var_region) x = Some sry &
         bytes = get_var_bytes (set_move_sub rmap x sr) sry.(sr_region) x]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        check_gvalid rmap y = Some (sry, bytes)]).
Proof.
  rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs' ws]|//] [<- <-].
    by right; split.
  case heq: Mvar.get => [sr'|//] [? <-]; subst sr'.
  case: (x =P y.(gv)).
  + move=> ?; subst x.
    by left.
  move=> hneq.
  right; split=> //.
  rewrite get_var_bytes_set_move_bytes.
  case: eqP => //= _.
  by move: hneq=> /eqP /negPf ->.
Qed.
(*
(* [arr_size] is sometimes automatically unfolded. We chose to unfold it
   everywhere, so that [lia] recognizes the identical terms.
   -> we made [arr_size] Opaque.
   TODO: move to WArray
   TODO: remove because now useless ?
*)
Lemma get_sub_get8 aa ws lena (a : WArray.array lena) len p a' aa' :
  WArray.get_sub aa ws len a p = ok a' ->
  forall ofs, 0 <= ofs < arr_size ws len ->
  WArray.get aa' U8 a' ofs = WArray.get aa' U8 a (p * mk_scale aa ws + ofs).
Proof.
  move=> hgsub ofs hofs.
(*   have hbound := get_sub_bound hgsub. *)
  rewrite !WArray.get8_read.
  rewrite (WArray.get_sub_get8 hgsub).
  by move: hofs; rewrite -!zify => ->.
Qed.
*)
(* For the general case, we have [type_of_get_gvar]. But it is imprecise due to
   the [word] case. We have a more precise result for arrays.
*)
Lemma type_of_get_gvar_array gd vm x n (a : WArray.array n) :
  get_gvar gd vm x = ok (Varr a) ->
  x.(gv).(vtype) = sarr n.
Proof.
  rewrite /get_gvar.
  case: (is_lvar x).
  + rewrite /get_var.
    apply on_vuP => //.
    case: x => -[[ty xn] xi] xs /=.
    by case: ty => //= len t _ [hty _]; f_equal.
  by move=> /type_of_get_global.
Qed.

Lemma get_Pvar_sub_bound s1 v e y suby ofs len :
  sem_pexpr gd s1 e = ok v ->
  get_Pvar_sub e = ok (y, suby) ->
  match suby with
  | Some p => p
  | None => (0, size_slot y.(gv))
  end = (ofs, len) ->
  0 < len /\
  0 <= ofs /\ ofs + len <= size_slot y.(gv).
Proof.
  case: e => //=.
  + move=> _ _ [_ <-] [<- <-].
    split; first by apply size_of_gt0.
    by lia.
  move=> aa ws len' x e'.
  apply: on_arr_gvarP.
  t_xrbindP=> n _ hty _ i v' he' hv' _ /get_sub_bound hbound _ ofs' hofs' <- <- [<- <-].
  split=> //.
  rewrite hty.
  have {he' hv'} he' : sem_pexpr gd s1 e' >>= to_int = ok i by rewrite he'.
  by move: hofs' => /(get_ofs_subP he') ->.
Qed.

Lemma get_Pvar_subP s1 n (a : WArray.array n) e y ofsy ofs len :
  sem_pexpr gd s1 e = ok (Varr a) ->
  get_Pvar_sub e = ok (y, ofsy) ->
  match ofsy with
  | None => (0%Z, size_slot y.(gv))
  | Some p => p
  end = (ofs, len) ->
  n = Z.to_pos len /\
  exists (t : WArray.array (Z.to_pos (size_slot y.(gv)))),
    get_gvar gd (evm s1) y = ok (Varr t) /\
    (forall i w, read a i U8 = ok w -> read t (ofs + i) U8 = ok w).
Proof.
  case: e => //=.
  + move=> y' hget [? <-] [<- ?]; subst y' len.
    have -> := type_of_get_gvar_array hget.
    split=> //.
    by exists a; split.
  move=> aa ws len' x e.
  apply: on_arr_gvarP.
  move=> n1 a1 hty hget.
  (* We manually apply [rbindP], because [t_xrbindP] is a bit too aggressive. *)
  apply: rbindP => i he.
  apply: rbindP => a2 hgsub heq.
  have := Varr_inj (ok_inj heq) => {heq} -[?]; subst n => /= ?; subst a2.
  t_xrbindP=> _ /(get_ofs_subP he) -> <- <- [<- <-].
  split=> //.
  rewrite hty.
  exists a1; split=> //.
  move=> k w.
  move=> /dup[]; rewrite -{1}get_read8 => /WArray.get_valid8 /WArray.in_boundP => hbound.
  rewrite (WArray.get_sub_get8 hgsub) /=.
  by move: hbound; rewrite -!zify => ->.
Qed.

Lemma is_stack_ptrP vpk s ofs ws z f :
  is_stack_ptr vpk = Some (s, ofs, ws, z, f) ->
  vpk = VKptr (Pstkptr s ofs ws z f).
Proof.
  case: vpk => [|[]] => //=.
  by move=> _ _ _ _ _ [-> -> -> -> ->].
Qed.

(* is mk_addr_pexpr a good name ?
   could be pexpr_addr_from_vpk ?
*)
Lemma mk_addr_pexprP rmap m0 s1 s2 (x : var_i) vpk sr e1 ofs :
  valid_state rmap m0 s1 s2 ->
  wf_vpk x vpk ->
  valid_vpk rmap s2 x sr vpk ->
  mk_addr_pexpr pmap rmap x vpk = ok (e1, ofs) ->
  exists w,
    sem_pexpr [::] s2 e1 >>= to_pointer = ok w /\
    sub_region_addr sr = (w + wrepr _ ofs)%R.
Proof.
  move=> hvs hwfpk hpk.
  rewrite /mk_addr_pexpr.
  case heq: is_stack_ptr => [[[[[s ws] ofs'] z] f]|]; last first.
  + by t_xrbindP=> -[x' ofs'] /(addr_from_vpkP hvs hwfpk hpk) haddr <- <-.
  move /is_stack_ptrP in heq; subst vpk.
  rewrite /= in hpk hwfpk.
  t_xrbindP=> _ /assertP /hpk hread <- <- /=.
  rewrite {1}/sub_region_addr /= (wfs_offset hwfpk) in hread.
  rewrite vs_rsp /= !zero_extend_u wrepr_add GRing.addrA hread /= truncate_word_u.
  eexists; split; first by reflexivity.
  by rewrite wrepr0 GRing.addr0.
Qed.

Lemma truncate_val_array n v v' :
  truncate_val (sarr n) v = ok v' ->
  exists m (a : WArray.array m) a',
    [/\ v = Varr a, WArray.cast n a = ok a' & v' = Varr a'].
Proof.
  rewrite /truncate_val /=.
  t_xrbindP=> a' /to_arrI [m [a [-> ha]]] <-.
  exists m, a, a'; split=> //.
Qed.

Lemma set_sub_bound aa ws lena (a : WArray.array lena) len p (b : WArray.array (Z.to_pos (arr_size ws len))) a' :
  WArray.set_sub aa a p b = ok a' ->
  0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= Z.pos lena.
Proof. by rewrite /WArray.set_sub; case: ifP => //; rewrite !zify. Qed.

(*
(* TODO: remove *)
Lemma set_sub_get8 aa ws lena (a : WArray.array lena) len p (b : WArray.array (Z.to_pos (arr_size ws len))) a' aa' :
  WArray.set_sub aa a p b = ok a' ->
  forall ofs,
  WArray.get aa' U8 a' ofs =
    let i := ofs - p * mk_scale aa ws in
    if (0 <=? i) && (i <? arr_size ws len) then
      WArray.get aa' U8 b i
    else WArray.get aa' U8 a ofs.
Proof.
  move=> hssub ofs.
(*   have hbound := set_sub_bound hssub. *)
  rewrite /= !WArray.get8_read.
  by apply (WArray.set_sub_get8 hssub).
Qed.

(* TODO: remove *)
Lemma cast_bound len len' (a : WArray.array len) a' :
  WArray.cast len' a = ok a' ->
  len' <= len.
Proof. apply WArray.cast_len. Qed.
*)

(* Alternative form of cast_get8 *)
(* Easier to use in our case *)
Lemma cast_get8 len1 len2 (m : WArray.array len2) (m' : WArray.array len1) :
  WArray.cast len1 m = ok m' ->
  forall k w,
    read m' k U8 = ok w ->
    read m k U8 = ok w.
Proof.
  move=> hcast k w.
  move=> /dup[]; rewrite -{1}get_read8 => /WArray.get_valid8 /WArray.in_boundP => hbound.
  rewrite (WArray.cast_get8 hcast).
  by case: hbound => _ /ZltP ->.
Qed.

Lemma valid_pk_set_move (rmap:region_map) s2 x sr y pk sry :
  ~ Sv.In x pmap.(vnew) ->
  wf_local y pk ->
  valid_pk rmap s2 sry pk ->
  valid_pk (set_move rmap x sr) s2 sry pk.
Proof.
  move=> hnnew hlocal.
  case: pk hlocal => //=.
  move=> s ofs ws z f hlocal.
  rewrite /check_stack_ptr get_var_bytes_set_move_bytes.
  case: eqP => [_|//].
  case: eqP => //.
  by have := hlocal.(wfs_new); congruence.
Qed.

Lemma wfr_VAL_set_move rmap s1 s2 x sr v :
  eq_sub_region_val x.(vtype) (emem s2) sr (get_var_bytes (set_move rmap x sr) sr.(sr_region) x) v ->
  wfr_VAL rmap s1 s2 ->
  wfr_VAL (set_move rmap x sr) (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) s2.
Proof.
  move=> heqval hval y sry bytesy vy /check_gvalid_set_move [].
  + move=> [? ? <- ->]; subst x.
    rewrite get_gvar_eq //.
    case: heqval => hread hty'.
    apply on_vuP => //; rewrite -hty'.
    by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty'.
  move=> [? hgvalid].
  rewrite get_gvar_neq => //.
  by apply hval.
Qed.

Lemma wfr_PTR_set_move (rmap : region_map) s2 x pk sr :
  get_local pmap x = Some pk ->
  valid_pk rmap s2 sr pk ->
  wfr_PTR rmap s2 ->
  wfr_PTR (set_move rmap x sr) s2.
Proof.
  move=> hlx hpk hptr y sry.
  have /wf_vnew hnnew := hlx.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists pk; split=> //.
    by apply (valid_pk_set_move _ hnnew (wf_locals hlx) hpk).
  move=> _ /hptr {pk hlx hpk} [pk [hly hpk]].
  exists pk; split=> //.
  by apply (valid_pk_set_move _ hnnew (wf_locals hly) hpk).
Qed.

(* There are 3 lemmas about [set_move] and [valid_state].
*)
Lemma valid_state_set_move rmap m0 s1 s2 x sr pk v :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some pk ->
  valid_pk rmap.(region_var) s2 sr pk ->
  eq_sub_region_val x.(vtype) (emem s2) sr (get_var_bytes (set_move rmap x sr) sr.(sr_region) x) v ->
  valid_state (set_move rmap x sr) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) s2.
Proof.
  move=> hvs hwf hlx hpk heqval.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor=> //=.
  + move=> y hget; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  case: (hwfr) => hwfsr hval hptr; split.
  + by apply (wfr_WF_set hwfsr hwf).
  + by apply (wfr_VAL_set_move heqval hval).
  by apply (wfr_PTR_set_move hlx hpk hptr).
Qed.

Lemma sub_region_at_ofs_0_wf sr ty :
  wf_sub_region sr ty ->
  wf_sub_region (sub_region_at_ofs sr (Some 0) (size_of ty)) ty.
Proof.
  move=> hwf.
  apply: (sub_region_at_ofs_wf hwf).
  by move=> _ [<-]; lia.
Qed.

(* Another lemma on [set_move] : we write in [evm s2].
   TODO: Fusionner les 2 lemmes sur set_move ??
   Ou supprimer celui-là qui est un peu spécifique ?
*)
Lemma valid_state_set_move_regptr rmap m0 s1 s2 x sr v p :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some (Pregptr p) ->
  eq_sub_region_val x.(vtype) (emem s2) sr (get_var_bytes (set_move rmap x sr) sr.(sr_region) x) v ->
  valid_state (set_move rmap x sr) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v])
                                      (with_vm s2 (evm s2).[p <- pof_val p.(vtype) (Vword (sub_region_addr sr))]).
Proof.
  move=> hvs hwf hlx heqval.
  have /wf_locals /= hlocal := hlx.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor=> //=.
  + rewrite get_var_neq //.
    by apply hlocal.(wfr_not_vrip).
  + rewrite get_var_neq //.
    by apply hlocal.(wfr_not_vrsp).
  + move=> y hget hnnew.
    rewrite get_var_neq; last by rewrite /get_local in hlx; congruence.
    rewrite get_var_neq; last by have := hlocal.(wfr_new); congruence.
    by apply heqvm.
  case: (hwfr) => hwfsr hval hptr; split.
  + by apply (wfr_WF_set hwfsr hwf).
  + move=> y sry bytesy vy.
    move=> /(check_gvalid_set_move) [].
    + move=> [? ? <- ->]; subst x.
      rewrite get_gvar_eq //.
      case: heqval => hread hty'.
      apply on_vuP => //; rewrite -hty'.
      by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty'.
    move=> [? hgvalid].
    rewrite get_gvar_neq => //.
    by apply hval.
  move=> y sry.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists (Pregptr p); split=> //=.
    rewrite get_var_eq.
    by rewrite hlocal.(wfr_rtype).
  move=> hneq /hptr [pk [hly hpk]].
  exists pk; split=> //.
  case: pk hly hpk => //=.
  + move=> p2 hly.
    rewrite get_var_neq //.
    by apply (hlocal.(wfr_distinct) hly hneq).
  move=> s ofs ws z f hly.
  rewrite /check_stack_ptr get_var_bytes_set_move_bytes.
  case: eqP => [_|//].
  case: eqP => //.
  have /is_sarrP [n hty] := hlocal.(wfr_type).
  have /wf_locals /wfs_new := hly.
  by have /wf_vnew := hlx; congruence.
Qed.

Lemma var_region_not_new rmap m0 s1 s2 x sr :
  valid_state rmap m0 s1 s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  ~ Sv.In x pmap.(vnew).
Proof. by move=> hvs /wfr_ptr [_ [/wf_vnew ? _]]. Qed.
(*
Lemma check_gvalid_set_stack_ptr rmap s1 s2 s ws z f y sry bytes :
  valid_state rmap m0 s1 s2 ->
  Sv.In f pmap.(vnew) ->
  check_gvalid (set_stack_ptr rmap s ws z f) y = Some (sry, bytes) ->
  exists bytes',
    [/\ check_gvalid rmap y = Some (sry, bytes'),
        ~ is_glob y -> f <> gv y &
        bytes =
          if (sub_region_stkptr s ws z).(sr_region) != sry.(sr_region) then bytes'
          else ByteSet.remove bytes' (interval_of_zone (sub_zone_at_ofs (sub_region_stkptr s ws z).(sr_zone) (Some 0) (wsize_size Uptr)))].
Proof.
  move=> hvs hnew.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs ws']|//] [<- <-].
    eexists; split=> //.
    by case: eqP.
  case heq: Mvar.get => [sr|//] [<- <-].
  have hneq: f <> y.(gv).
  + by move /var_region_not_new : heq; congruence.
  eexists; split=> //.
  rewrite get_var_bytes_set_pure_bytes.
  by have /eqP /negPf -> := hneq.
Qed.
*)
Lemma check_gvalid_set_stack_ptr rmap m0 s1 s2 s ws z f y sry bytes x sr :
  valid_state rmap m0 s1 s2 ->
  ~ Sv.In x pmap.(vnew) ->
  Sv.In f pmap.(vnew) ->
  check_gvalid (set_stack_ptr (set_move rmap x sr) s ws z f) y = Some (sry, bytes) ->
  exists bytes',
    [/\ check_gvalid (set_move rmap x sr) y = Some (sry, bytes'),
        ~ is_glob y -> f <> gv y &
        bytes =
          if (sub_region_stkptr s ws z).(sr_region) != sry.(sr_region) then bytes'
          else ByteSet.remove bytes' (interval_of_zone (sub_zone_at_ofs (sub_region_stkptr s ws z).(sr_zone) (Some 0) (wsize_size Uptr)))].
Proof.
  move=> hvs hnnew hnew.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs ws']|//] [<- <-].
    eexists; split=> //.
    by case: eqP.
  case heq: Mvar.get => [sr'|//] [<- <-].
  have hneq: f <> y.(gv).
  + move: heq; rewrite Mvar.setP.
    case: eqP => [|_].
    + by congruence.
    by move=> /var_region_not_new; congruence.
  eexists; split=> //.
  rewrite get_var_bytes_set_pure_bytes.
  by have /eqP /negPf -> := hneq.
Qed.

Lemma valid_pk_set_stack_ptr (rmap : region_map) s2 x s ofs ws z f mem2 y pk sr:
  wf_stkptr x s ofs ws z f ->
  (forall p ws,
    disjoint_range (sub_region_addr (sub_region_stkptr s ws z)) Uptr p ws ->
    read mem2 p ws = read (emem s2) p ws) ->
  x <> y ->
  get_local pmap y = Some pk ->
  valid_pk rmap s2 sr pk ->
  valid_pk (set_stack_ptr rmap s ws z f) (with_mem s2 mem2) sr pk.
Proof.
  move=> hlocal hreadeq hneq.
  case: pk => //= s1 ofs1 ws1 z1 f1 hly hpk.
  have hwf := sub_region_stkptr_wf hlocal.
  assert (hwf1 := sub_region_stkptr_wf (wf_locals hly)).
  rewrite /check_stack_ptr get_var_bytes_set_pure_bytes.
  case: eqP => heqr /=.
  + have hneqf := hlocal.(wfs_distinct) hly hneq.
    have /eqP /negPf -> := hneqf.
    move=> /mem_remove [] /hpk <-.
    rewrite disjoint_interval_of_zone // => hdisj.
    apply hreadeq.
    by apply (disjoint_zones_disjoint_zrange hwf hwf1 heqr).
  move=> /hpk <-.
  apply hreadeq.
  apply (disjoint_zrange_incl (zbetween_sub_region_addr hwf) (zbetween_sub_region_addr hwf1)).
  apply (disjoint_writable hwf.(wfr_slot) hwf1.(wfr_slot)); last by rewrite hwf.(wfr_writable).
  by move=> /(wf_region_slot_inj hwf hwf1).
Qed.

Lemma valid_state_set_stack_ptr rmap m0 s1 s2 x s ofs ws z f mem2 sr v :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  get_local pmap x = Some (Pstkptr s ofs ws z f) ->
  (forall p ws,
    validw mem2 p ws = validw (emem s2) p ws) ->
  (forall p ws,
    disjoint_range (sub_region_addr (sub_region_stkptr s ws z)) Uptr p ws ->
    read mem2 p ws = read (emem s2) p ws) ->
  read mem2 (sub_region_addr (sub_region_stkptr s ws z)) U64 = ok (sub_region_addr sr) ->
  eq_sub_region_val x.(vtype) (emem s2) sr (get_var_bytes (set_move rmap x sr) sr.(sr_region) x) v ->
  valid_state (set_stack_ptr (set_move rmap x sr) s ws z f) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) (with_mem s2 mem2).
Proof.
  move=> hvs hwf hlx hvalideq hreadeq hreadptr heqval.
  have hreadeq': forall p ws,
    disjoint_range (sub_region_addr (sub_region_at_ofs (sub_region_stkptr s ws z) (Some 0) (wsize_size U64))) Uptr p ws ->
    read mem2 p ws = read (emem s2) p ws.
  + by move=> ??; rewrite -sub_region_addr_offset wrepr0 GRing.addr0; apply hreadeq.
  have /wf_locals hlocal := hlx.
  have hwfs := sub_region_stkptr_wf hlocal.
  have hwfs' := sub_region_at_ofs_0_wf hwfs.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor=> //=.
  + by move=> ??; rewrite hvalideq; apply hvalid.
  + by move=> ??; rewrite hvalideq; apply hincl.
  + by apply (mem_unchanged_write_slot hwfs refl_equal hreadeq hunch).
  + move=> y hget; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  case: (hwfr) => hwfsr hval hptr; split.
  + by apply (wfr_WF_set hwfsr hwf).
  + move=> y sry bytesy vy /(check_gvalid_set_stack_ptr hvs (wf_vnew hlx) hlocal.(wfs_new)).
    move=> {bytesy} [bytesy [hgvalidy ? ->]] hgety.
    have /(check_gvalid_wf (wfr_WF_set hwfsr hwf _)) -/(_ refl_equal) hwfy := hgvalidy.
    assert (heqvaly := wfr_VAL_set_move heqval wfr_val hgvalidy hgety).
    case: eqP => heqr /=.
    + by apply (eq_sub_region_val_same_region hwfs' hwfy heqr hreadeq' heqvaly).
    by apply (eq_sub_region_val_disjoint_regions hwfs' hwfy heqr refl_equal hreadeq' heqvaly).
  + move=> y sry.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- [<-].
      by exists (Pstkptr s ofs ws z f); split.
    move=> hneq /wfr_ptr [pky [hly hpky]].
    exists pky; split=> //.
    apply (valid_pk_set_stack_ptr hlocal hreadeq hneq hly).
    by apply (valid_pk_set_move sr (wf_vnew hlx) (wf_locals hly) hpky).
  by apply (eq_mem_source_write_slot hvs hwfs hreadeq).
Qed.

Lemma valid_state_set_move_sub rmap m0 s1 s2 x pk v sr :
  valid_state rmap m0 s1 s2 ->
  get_local pmap x = Some pk ->
  (forall srx, Mvar.get rmap.(var_region) x = Some srx ->
    eq_sub_region_val x.(vtype) (emem s2) srx (get_var_bytes (set_move_sub rmap x sr) srx.(sr_region) x) v) ->
  valid_state (set_move_sub rmap x sr) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) s2.
Proof.
  move=> hvs hlx heqval.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor => //=.
  + move=> y hgety; rewrite get_var_neq; first by apply heqvm.
    by rewrite /get_local in hlx; congruence.
  case: (hwfr) => hwfsr hval hptr; split=> //.
  + move=> y sry bytesy vy.
    move=> /check_gvalid_set_move_sub [].
    + move=> [? ? hget ->]; subst x.
      case: (heqval _ hget) => hread hty.
      rewrite get_gvar_eq //.
      apply on_vuP => //; rewrite -hty.
      by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty.
    move=> [? hgvalid].
    rewrite get_gvar_neq => //.
    by apply hval.
  move=> y sry.
  move=> /hptr [pky [hly hpky]].
  exists pky; split=> //.
  case: pky hly hpky => //=.
  move=> s ofs' ws z f hly heq.
  rewrite /check_stack_ptr get_var_bytes_set_move_bytes.
  case: eqP => // _.
  case: eqP => //.
  have /wf_vnew := hlx.
  by have /wf_locals /wfs_new := hly; congruence.
Qed.

(* This reasoning appears both in [alloc_array_moveP] and [alloc_array_move_initP],
   therefore we factorize it in this lemma.
   Note that we assume [eq_sub_region_val_read] only on the (sub-)sub-region
   [sub_region_at_ofs sr (Some ofs) len]. We do not need it for the full
   sub-region [sr], since we can derive it for the rest of [sr] from
   the [valid_state] hypothesis.
*)
Lemma valid_state_set_move_sub_write_lval rmap m0 s1 s2 r x ofsx ofs len n (a : WArray.array n) s1' pk sr :
  valid_state rmap m0 s1 s2 ->
  get_Lvar_sub r = ok (x, ofsx) ->
  match ofsx with
  | Some p => p
  | None => (0, size_slot x)
  end = (ofs, len) ->
  write_lval gd r (Varr a) s1 = ok s1' ->
  get_local pmap x = Some pk ->
  (forall srx, Mvar.get rmap.(var_region) x = Some srx -> srx = sr) ->
  let: rmap2 := set_move_sub rmap x (sub_region_at_ofs sr (Some ofs) len) in
  eq_sub_region_val_read (emem s2) (sub_region_at_ofs sr (Some ofs) len) (get_var_bytes rmap2 sr.(sr_region) x) (Varr a) ->
  valid_state rmap2 m0 s1' s2.
Proof.
  move=> hvs.
  set valid_state := valid_state. (* hack due to typeclass interacting badly *)
  case: r => //=.
  + move=> _ [-> <-] [<- <-].
    rewrite /write_var; t_xrbindP=> vm1'; apply: set_varP; last first.
    + by move=> /is_sboolP h1 h2; elimtype False; move: h2; rewrite h1.
    case: x => -[xty xn] xii; case: xty => //=.
    move=> nx ax hax <- <-.
    set x := {| vname := xn |} => hlx hget hread.
    rewrite -(WArray.castK ax).
    apply (valid_state_set_move_sub hvs hlx (v:=Varr ax)).
    move=> _ /hget ->.
    split=> // off hmem w /(cast_get8 hax) /hread.
    (* TODO: can we do something nicer than [Z.add_0_r]? *)
    rewrite -sub_region_addr_offset wrepr0 GRing.addr0 /= Z.add_0_r.
    by apply.

  t_xrbindP=> aa ws {len}len _ e ofs' hofs -> <- [? <-]; subst ofs'.
  apply: on_arr_varP.
  t_xrbindP=> nx ax htyx hxa i v he hv a2 ha2 a3 ha3 vm1'.
  have {he hv} he : sem_pexpr gd s1 e >>= to_int = ok i.
  + by rewrite he.
  have {hofs} -> := get_ofs_subP he hofs.
  apply: set_varP; last by rewrite {1}htyx.
  case: x htyx hxa => -[_ xn] xii /= ->.
  set x := {| vname := xn |} => hxa /= _ <- <- <- hlx hget hread.
  apply (valid_state_set_move_sub hvs hlx (v := Varr a3)).
  move=> srx /dup[] /hget{hget} ? hget; subst srx.
  split=> // off hmem w /=.
  rewrite (WArray.set_sub_get8 ha3) /=.
  case: ifPn => [_|].
  + move=> /(cast_get8 ha2).
    move: hmem w.
    rewrite -{1 3}(Zplus_minus (i * mk_scale aa ws) off).
    move: {off} (off - i * mk_scale aa ws) => off.
    rewrite wrepr_add GRing.addrA (sub_region_addr_offset (arr_size ws len)) Z.add_assoc.
    by apply hread.
  rewrite !zify => hbound.
  have hgvalid := check_gvalid_lvar (x:={|v_var := x; v_info := xii|}) hget.
  case: (wfr_val hgvalid hxa) => hread' _.
  apply hread'.
  move: hmem.
  rewrite get_var_bytes_set_move_bytes !eq_refl /=.
  rewrite ByteSet.addE => /orP [|//].
  by rewrite /I.memi /= !zify; lia.
Qed.

Lemma lea_ptrP s1 e i x ofs w s2 :
  sem_pexpr [::] s1 e >>= to_pointer = ok i ->
  write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2 ->
  sem_i P' w s1 (lea_ptr x e ofs) s2.
Proof.
  move=> he hx.
  constructor.
  rewrite /sem_sopn /= P'_globs /sem_sop2 /=.
  move: he; t_xrbindP=> _ -> /= -> /=.
  by rewrite !zero_extend_u hx.
Qed.

Lemma mov_ptrP s1 e i x w s2 :
  sem_pexpr [::] s1 e >>= to_pointer = ok i ->
  write_lval [::] x (Vword i) s1 = ok s2 ->
  sem_i P' w s1 (mov_ptr x e) s2.
Proof.
  move=> he hx.
  constructor.
  rewrite /sem_sopn P'_globs /= /exec_sopn /=.
  move: he; t_xrbindP=> _ -> /= -> /=.
  by rewrite hx.
Qed.

Lemma mov_ofsP s1 e i x ofs w mk s2 :
  sem_pexpr [::] s1 e >>= to_pointer = ok i ->
  write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2 ->
  sem_i P' w s1 (mov_ofs x mk e ofs) s2.
Proof.
  case: mk.
  + by apply lea_ptrP.
  rewrite /=.
  case: eqP => [->|_].
  + rewrite wrepr0 GRing.addr0.
    by apply mov_ptrP.
  by apply lea_ptrP.
Qed.

Lemma wf_sub_region_subtype sr ty1 ty2 :
  subtype ty2 ty1 ->
  wf_sub_region sr ty1 ->
  wf_sub_region sr ty2.
Proof.
  move=> hsub [hwf1 [hwf2 hwf3]]; split=> //; split=> //.
  by move /size_of_le : hsub; lia.
Qed.

Lemma alloc_array_moveP m0 s1 s2 s1' rmap1 rmap2 r e v v' n i2 : 
  valid_state rmap1 m0 s1 s2 ->
  sem_pexpr gd s1 e = ok v ->
  truncate_val (sarr n) v = ok v' ->
  write_lval gd r v' s1 = ok s1' ->
  alloc_array_move pmap rmap1 r e = ok (rmap2, i2) → 
  ∃ s2' : estate, sem_i P' rip s2 i2 s2' ∧ valid_state rmap2 m0 s1' s2'.
Proof.
  move=> hvs he htr hw.
  have [m [a [a' [? ha' ?]]]] := truncate_val_array htr; subst v v'.
  rewrite /alloc_array_move.
  t_xrbindP=> -[x ofsx] hgetr [y ofsy] hgete.
  case hkindy: (get_var_kind pmap y) => [vk|] //.
  case hofsy: (match ofsy with
               | Some p => p
               | None => (0, size_slot (gv y))
               end) => [ofs len].
  case: vk hkindy => [vpky|//] hkindy.
  have [hlen hofs] := get_Pvar_sub_bound he hgete hofsy.
  have hofs': forall zofs, Some ofs = Some zofs -> 0 <= zofs /\ zofs + len <= size_slot y.(gv).
  + by move=> _ [<-].
  t_xrbindP=> -[[[sry' mk] ey] ofs2'] _ <-.
  t_xrbindP=> -[sry _] /(check_vpkP hofs' hkindy) [bytesy [hgvalidy -> hmemy]].
  assert (hwfy := check_gvalid_wf wfr_wf hgvalidy).
  have hwfy': wf_sub_region (sub_region_at_ofs sry (Some ofs) len) (sarr (Z.to_pos len)).
  + move: hofs'.
    have {1 2}-> : len = size_of (sarr (Z.to_pos len)) by rewrite /= Z2Pos.id.
    by apply: (sub_region_at_ofs_wf hwfy).
  have hwfpky := get_var_kind_wf hkindy.
  have hpky: valid_vpk rmap1 s2 y.(gv) sry vpky.
  + have /wfr_gptr := hgvalidy.
    by rewrite hkindy => -[_ [[]] <-].
  move=> [e1 ofs2] /(mk_addr_pexprP _ hwfpky hpky) [w [he1 haddr]] ? <- <- ?; subst sry' ofs2'.
  have [? [ay [hgety hay]]] := get_Pvar_subP he hgete hofsy; subst m.

  have hread: forall bytes,
    eq_sub_region_val_read (emem s2) (sub_region_at_ofs sry (Some ofs) len) bytes (Varr a').
  + move=> bytes off hmem w' /(cast_get8 ha') /dup[].
    rewrite -{1}get_read8 => /WArray.get_valid8 /WArray.in_boundP; rewrite Z2Pos.id // => hoff.
    move=> /hay.
    rewrite -sub_region_addr_offset -GRing.addrA -wrepr_add.
    assert (hval := wfr_val hgvalidy hgety).
    case: hval => hread _.
    apply hread.
    rewrite memi_mem_U8; apply: subset_mem hmemy; rewrite subset_interval_of_zone.
    rewrite -(sub_zone_at_ofs_compose _ _ _ len).
    apply zbetween_zone_byte => //.
    by apply zbetween_zone_refl.

  case: r hgetr hw => //.
  + move=> _ [-> <-].
    rewrite /write_lval /write_var; t_xrbindP=> vm1'; apply: set_varP; last first.
    + by move=> /is_sboolP h1 h2; elimtype False; move: h2; rewrite h1.
    case: x => -[xty xn] xii; case: xty => //=.
    move=> nx ax hax <- <-.
    set x := {| vname := xn |}.
    case hlx: (get_local pmap x) => [pk|//].
    have /wf_locals hlocal := hlx.

    have heqval: forall bytes,
      eq_sub_region_val x.(vtype) (emem s2) (sub_region_at_ofs sry (Some ofs) len)
                        bytes (Varr ax).
    + move=> bytes.
      by split=> // off /hread{hread}hread w' /(cast_get8 hax) /hread.

    have hwf: wf_sub_region (sub_region_at_ofs sry (Some ofs) len) x.(vtype).
    + apply: (wf_sub_region_subtype _ hwfy').
      apply /ZleP.
      by apply: Z.le_trans (WArray.cast_len hax) (WArray.cast_len ha').

    rewrite -(WArray.castK ax).

    case: pk hlx hlocal.
    + t_xrbindP=> s ofs' ws z sc hlx hlocal _ /assertP /eqP heqsub <- <-.
      exists s2; split; first by constructor.
      (* valid_state update *)
      by apply: (valid_state_set_move hvs hwf hlx _ (heqval _)).
    + move=> p hlx hlocal [<- <-].
      set vp := pof_val p.(vtype) (Vword (sub_region_addr (sub_region_at_ofs sry (Some ofs) len))).
      exists (with_vm s2 (evm s2).[p <- vp]); split.
      + rewrite /vp -sub_region_addr_offset haddr -GRing.addrA -wrepr_add.
        apply (mov_ofsP _ _ he1).
        by case: (p) hlocal.(wfr_rtype) => ? pn /= ->.
      (* valid_state update *)
      by apply (valid_state_set_move_regptr hvs hwf hlx (heqval _)).
    move=> s ofs' ws z f hlx hlocal [<- hi2].

    have {hi2} [mem2 [hsemi hvalideq hreadeq hreadptr]]:
      exists mem2,
      [/\ sem_i P' rip s2 i2 (with_mem s2 mem2),
          (forall p ws, validw mem2 p ws = validw (emem s2) p ws),
          (forall p ws,
            disjoint_range (sub_region_addr (sub_region_stkptr s ws z)) U64 p ws ->
            read mem2 p ws = read (emem s2) p ws) &
          read mem2 (sub_region_addr (sub_region_stkptr s ws z)) U64 =
            ok (sub_region_addr (sub_region_at_ofs sry (Some ofs) len))].
    + subst i2.
      case: ifP.
      + case heq: Mvar.get => [srx|//] /andP [/eqP heqsub hcheck].
        exists (emem s2); split=> //.
        + by rewrite with_mem_same; constructor.
        + have /wfr_ptr := heq; rewrite hlx => -[_ [[<-] hpk]].
          rewrite -heqsub.
          by apply hpk.
      have hwfs := sub_region_stkptr_wf hlocal.
      have hvp: validw (emem s2) (sub_region_addr (sub_region_stkptr s ws z)) Uptr.
      + apply (validw_sub_region_addr hvs hwfs).
        by apply (is_align_sub_region_stkptr hlocal).
      have /writeV -/(_ (w + wrepr U64 (ofs2 + ofs))%R) [mem2 hmem2] := hvp.
      exists mem2; split.
      + apply (mov_ofsP _ _ he1).
        rewrite /= vs_rsp /= !zero_extend_u.
        by rewrite wrepr_add GRing.addrA -hlocal.(wfs_offset) hmem2.
      + by move=> ??; apply (write_validw_eq hmem2).
      + by move=> ??; apply (writeP_neq hmem2).
      rewrite (writeP_eq hmem2).
      by rewrite wrepr_add GRing.addrA -haddr -sub_region_addr_offset.

    exists (with_mem s2 mem2); split=> //.
    by apply (valid_state_set_stack_ptr hvs hwf hlx hvalideq hreadeq hreadptr (heqval _)).

  (* interestingly, we can prove that n = Z.to_pos len = Z.to_pos (arr_size ws len2)
     but it does not seem useful
  *)
  move=> aa ws len2 x' e' hgetr hw.
  have /= := hgetr; t_xrbindP=> ofs3 hofs3 ? ?; subst x' ofsx.
  case hlx: (get_local pmap x) => [pk|//].
  t_xrbindP=> _ /set_arr_subP [srx [hgetx heqsub <-]] <- <-.
  exists s2; split; first by constructor.
  apply (valid_state_set_move_sub_write_lval hvs hgetr refl_equal hw hlx).
  + by move=> ?; rewrite hgetx => -[].
  by rewrite heqsub.
Qed.

Lemma is_array_initP e : reflect (exists n, e = Parr_init n) (is_array_init e).
Proof.
  case: e => /=; constructor; try by move => -[].
  by eexists.
Qed.

Lemma get_Lvar_sub_bound s1 s1' v r x subx ofs len :
  write_lval gd r v s1 = ok s1' ->
  get_Lvar_sub r = ok (x, subx) ->
  match subx with
  | Some p => p
  | None => (0, size_slot x)
  end = (ofs, len) ->
  0 < len /\
  0 <= ofs /\ ofs + len <= size_slot x.
Proof.
  case: r => //=.
  + move=> _ _ [_ <-] [<- <-].
    split; first by apply size_of_gt0.
    by lia.
  move=> aa ws len' x' e.
  apply: on_arr_varP.
  t_xrbindP=> n _ hty _ i v' he hv' _ _ _ /set_sub_bound hbound _ _ _ ofs' hofs' <- <- [<- <-].
  split=> //.
  rewrite hty.
  have {he hv'} he : sem_pexpr gd s1 e >>= to_int = ok i by rewrite he.
  by move: hofs' => /(get_ofs_subP he) ->.
Qed.

Lemma alloc_array_move_initP m0 s1 s2 s1' rmap1 rmap2 r e v v' n i2 : 
  valid_state rmap1 m0 s1 s2 ->
  sem_pexpr gd s1 e = ok v ->
  truncate_val (sarr n) v = ok v' ->
  write_lval gd r v' s1 = ok s1' ->
  alloc_array_move_init pmap rmap1 r e = ok (rmap2, i2) → 
  ∃ s2' : estate, sem_i P' rip s2 i2 s2' ∧ valid_state rmap2 m0 s1' s2'.
Proof.
  move=> hvs.
  rewrite /alloc_array_move_init.
  case: is_array_initP; last first.
  + by move=> _; apply alloc_array_moveP.
  move=> [m ->] /= [<-].
  rewrite /truncate_val /=.
  t_xrbindP=> _ /WArray.cast_empty_ok -> {m} <- hw [x ofsx] hgetr.
  case hofsx: (match ofsx with
               | Some p => p
               | None => (0, size_slot x)
               end) => [ofs len].
  case hlx: get_local => [pk|//].
  t_xrbindP=> sr hsr <- <-.
  exists s2; split; first by constructor.
  (* valid_state update *)
  apply (valid_state_set_move_sub_write_lval hvs hgetr hofsx hw hlx).
  + move=> srx hgetx.
    case: pk hlx hsr.
    + move=> s ofs' ws z [] // hlx [<-].
      have /wfr_ptr := hgetx.
      by rewrite hlx => -[_ [[<-] ->]].
    + by move=> _ _ /get_sub_regionP; congruence.
    by move=> _ _ _ _ _ _ /get_sub_regionP; congruence.
  move=> off hmem w /=.
  by rewrite WArray.get_empty; case: ifP.
Qed.

(*
Search add_iinfo.
    case:x hv htr Hw => [??| x|???|????]; try by apply: alloc_assgnP.
(*    case: ifP => hty. last by apply: alloc_assgnP.
    case he : is_var => [y | ]; last by apply: alloc_assgnP.
    case: ifP => hsubty; last by apply: alloc_assgnP.
    case hf : find_gvar => [mp | ]; last by apply: alloc_assgnP.
    move=> hv htr Hw; have [n htyx] := is_arr_typeP hty; have ? := is_varP he; subst e.
    set x' := {| v_var := _ |}.
    t_xrbindP => -[_sm2 _i2] _tt; apply: add_iinfoP=> /check_vfresh_lvalP [hnrsp hnrip] [??] /= ??? s1' hva.
    subst _sm2 ii1 _i2 i2 sm2; have := valid_s hva y. 
    rewrite hf => -[h1 h2].
    set s2' := {| emem := emem s1';
                  evm := (evm s1').[x' <- ok (@Build_pword U64 U64 
                                               (wptr (mp_s mp) + wrepr U64 (mp_ofs mp))
                                               (erefl true))] |}.
    exists s2'; split.
    + case hid: mp_id h1 => [idx | ] /= h1.
      + apply: S.Eassgn => /=;eauto.
        + by rewrite /truncate_val /= zero_extend_u; auto.
        done.
      apply: S.Eopn; rewrite /sem_sopn /= /get_gvar /= (get_vptr hva) /= /s2'. 
      by do 5! f_equal;rewrite !zero_extend_u wrepr0 wrepr1; ssrring.ssring.
    move: Hw; apply rbindP =>vm1 /=; apply: set_varP;rewrite /set_var; last by rewrite {1}htyx.
    move=> t ht ?[?]; subst vm1 s2.
    move: hv; rewrite /= /s2' /x' => {s2' x'}.
    case: x hnrsp hnrip hty htyx hsubty t ht => -[xty xn] xi /= hnrsp hnrip hty htyx hsubty t ht /=.
    subst xty; case: v' htr ht => // n' a'; last first.
    + by rewrite /pof_val /=; case: (n').
    rewrite /truncate_val; t_xrbindP; case: ty => //= n1 yt.
    case: v => //=;last by case.
    move=> ny ty1 /=; rewrite /WArray.cast; case: ifP => // /ZleP hn1 [?].
    move=> /Varr_inj [?]; subst n1 => /= ? [?] hgety; subst yt t a'. 
    have hyty: vtype (gv y) = sarr ny.  
    + move: hgety; rewrite /get_gvar; case: ifP => ?.
      + rewrite /get_var; apply on_vuP => //.
        by case: (gv y) => -[] [] //= p ???? /Varr_inj [?]; subst p. 
      by rewrite /get_global; case: get_global_value => // ?; case: eqP => // <- [->].
    move: hsubty; rewrite hyty /= => /ZleP hsubty.
    case: hva => hd her hdef hvm hrip hrsp htop hfr hs hm hg {h1 he}; split => //=.
    + move=> z /= /Sv_memP hin; rewrite !Fv.setP_neq; first last.
      + by apply /eqP; SvD.fsetdec. + by apply /eqP; SvD.fsetdec.
      by apply: hvm; apply /Sv_memP; SvD.fsetdec.
    + by rewrite get_var_neq // => h; move: hnrip; rewrite h /is_vrip eq_refl.
    + by rewrite get_var_neq // => h; move: hnrsp; rewrite h /is_vrsp eq_refl.
    + move=> z; case heq: find_gvar => [mpz | //]; move: heq.
      rewrite find_gvar_set; case: andP => [ [hlv /eqP heq] [?]| hna].
      + subst mpz => /=; split; first by rewrite /get_var Fv.setP_eq.
        move: h2; rewrite -heq /= hyty => h off hoff.
        have hoff' : 0 <= off ∧ off < ny by lia.
        have [h1 /(_ _ _ hgety) h2]:= h _ hoff'; split => //.
        rewrite /get_gvar hlv -heq /get_var Fv.setP_eq /= => s' a hok. 
        have /Varr_inj [? {hok}]:= ok_inj hok.
        subst s' => /= ? v hv; subst a; apply h2. 
        apply: WArray.uincl_get hv; split => // i vi hi.
        by rewrite WArray.zget_inject //=; case: ifP.
      move=> /find_gvar_keep [hz hdiff] /=.
      have := hs z; rewrite hz => -[hz1 hz2]; split.
      + case: mp_id hdiff hz1 => // id hne.
        by rewrite get_var_neq // => -[eid]; apply hne;rewrite eid.
      case: vtype hz2 => //.
      + move=> p hp off; rewrite get_gvar_neq; first by apply hp.
        by move=> his; apply /negP => he;auto.
      move=> w [hw1 hw2]; split => // v; rewrite get_gvar_neq; first by apply hw2.
      by move=> his; apply /negP => he;auto.
    move=> z mpz; have := hm _ _ hf; rewrite hyty => -[nn [[?]]]; subst nn.
    move=> [hmp1 hmp2 hmp3 hmp4].
    rewrite find_gvar_set;case: andP => [ [hlv /eqP heq] [?]| hna].
    + subst mpz => /=; exists n; rewrite -heq /=; split => //; split => //; first by lia.
      move=> z1 mpz1 sz1;rewrite find_gvar_set;case: andP => [ [hlv1 /eqP heq1] [?]| hna1].
      + by subst mpz1; rewrite /= eq_refl -heq1 /= => ?? [].
      move=> /find_gvar_keep [hz1 hdiff] /= hsz hms. 
      have := hmp4 _ _ _ hz1 hsz hms; case:eqP;last by lia.
      move=> ? h1 [ //| hh1]; have heq1 := h1 (or_intror hh1).
      by move: hh1; rewrite -heq1 hyty.
    move=> /find_gvar_keep [hz1 hdiff].
    have [sz1 [hsz1 [hmpz1 hmpz2 hmpz3 hmpz4]]]:= hm _ _ hz1; exists sz1; split => //; split => //.
    move => s mps ss;rewrite find_gvar_set;case: andP => [ [hlv1 /eqP heq1] [?]| hna1].
    + subst mps => /=; rewrite -heq1 /= => -[?] h1; subst ss.
      have := hmp4 _ _ _ hz1 hsz1; rewrite h1 => /(_ erefl); rewrite eq_sym.
      case: eqP => ?; last lia.
      move=> h [ hh1| //]; have heq2 := h (or_intror hh1).
      by move: hh1; rewrite -heq2 hyty.
    move=> /find_gvar_keep [hh1 hh2 hh3 hh4].
    by apply: hmpz4 hh1 hh3 hh4. *)
  Qed.
  *)

Inductive Forall3 (A B C : Type) (R : A → B -> C -> Prop) : seq A → seq B → seq C -> Prop :=
    Forall3_nil : Forall3 R [::] [::] [::]
  | Forall3_cons : ∀ (a : A) (b : B) (c : C) (la : seq A) (lb : seq B) (lc : seq C),
                     R a b c → Forall3 R la lb lc → Forall3 R (a :: la) (b :: lb) (c :: lc).

(* Rin: link between the values given as arguments in the source and the target. *)
(* TODO: exists p or exists sr, ... (sub_region_addr sr) ? *)
Definition Rin_aux m sao_param va va' :=
    match sao_param with
    | None => va' = va
    | Some pi =>
      exists p,
        va' = Vword p /\
        is_align p pi.(pp_align) /\
        forall off w, get_val_byte va off = ok w -> read m (p + wrepr _ off)%R U8 = ok w
    end.

(* Rout: link between the values returned by the function in the source and the target. *)
Definition Rout_aux m (i : option nat) vr vr' :=
    if i is None then
      vr' = vr
    else
      exists p,
        vr' = Vword p /\
        forall off w, get_val_byte vr off = ok w -> read m (p + wrepr _ off)%R U8 = ok w.

Lemma get_PvarP e x : get_Pvar e = ok x -> e = Pvar x.
Proof. by case: e => //= _ [->]. Qed.

Lemma alloc_call_argP m0 rmap s1 s2 sao_param e v osr e' :
  valid_state rmap m0 s1 s2 ->
  alloc_call_arg pmap rmap sao_param e = ok (osr, e') ->
  sem_pexpr gd s1 e = ok v ->
  exists v',
    sem_pexpr [::] s2 e' = ok v' /\
    Rin_aux (emem s2) sao_param v v'.
Proof.
  move=> hvs.
  rewrite /alloc_call_arg.
  t_xrbindP=> x /get_PvarP -> _ /assertP.
  case: x => x [] //= _.
  case: sao_param => [pi|]; last first.
  + case hlx: get_local => //.
    t_xrbindP=> _ /check_diffP hnnew _ <- /= hget.
    have hkind: get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    have hget2 := get_var_kindP hvs hkind hnnew hget.
    by exists v.
  + case hlx: get_local => [pk|//].
    case: pk hlx => // p hlx.
    t_xrbindP=> -[sr _] /check_validP [bytes [hgvalid -> hmem]] ? hwritable.
    assert (hwf := check_gvalid_wf wfr_wf hgvalid).
    move=> _ /(check_alignP hwf) halign _ <- /= hget.
    have /wfr_gptr := hgvalid.
    rewrite /get_var_kind /= hlx => -[_ [[<-] /=]].
    rewrite get_gvar_nglob // => ->.
    eexists; split; first by reflexivity.
    eexists; split; first by reflexivity.
    split=> //.
    move=> off w /dup[] /get_val_byte_bound hbound.
    assert (hval := wfr_val hgvalid hget).
    case: hval => hread hty.
    rewrite hty in hbound.
    apply hread.
    rewrite memi_mem_U8; apply: subset_mem hmem; rewrite subset_interval_of_zone.
    rewrite -(Z.add_0_l off).
    rewrite -(sub_zone_at_ofs_compose _ _ _ (size_slot x)).
    apply zbetween_zone_byte => //.
    by apply zbetween_zone_refl.
Qed.

Lemma alloc_call_args_test rmap sao_params args l :
  alloc_call_args pmap rmap sao_params args = ok l ->
    forall i1 b1 sr1 i2 b2 sr2 e1 x1 e2 x2,
      nth None (map fst l) i1 = Some (b1, sr1) ->
      nth None (map fst l) i2 = Some (b2, sr2) ->
      nth (Pconst 0) args i1 = e1 -> get_Pvar e1 = ok x1 ->
      nth (Pconst 0) args i2 = e2 -> get_Pvar e2 = ok x2 ->
      i1 <> i2 ->
      b1 ->
      disjoint_zrange (sub_region_addr sr1) (size_slot x1.(gv)) (sub_region_addr sr2) (size_slot x2.(gv)).
Proof.
Admitted.

Lemma alloc_call_argsP m0 rmap s1 s2 sao_params args vargs l :
  valid_state rmap m0 s1 s2 ->
  alloc_call_args pmap rmap sao_params args = ok l ->
  sem_pexprs gd s1 args = ok vargs ->
  exists vargs',
    sem_pexprs [::] s2 (map snd l) = ok vargs' /\
    Forall3 (Rin_aux (emem s2)) sao_params vargs vargs'.
(*     Forall (fun '(osr, _) => match osr with ..) *)
Proof.
  move=> hvs.
  rewrite /alloc_call_args.
  t_xrbindP=> {l}l hmap _ _ <-.
  elim: sao_params args l vargs hmap.
  + move=> [|//] /= _ _ [<-] [<-].
    eexists; split; first by reflexivity.
    by constructor.
  move=> pi sao_params ih [//|arg args] l' vargs /=.
  t_xrbindP=> -[osr e] halloc l hmap ? varg hvarg vargs' hvargs' ?; subst l' vargs.
  rewrite /=.
  have [varg' [hvarg' hin]] := (alloc_call_argP hvs halloc hvarg).
  have [vargs'' [hvargs'' hin']] := ih _ _ _ hmap hvargs'.
  rewrite hvarg' hvargs'' /=.
  eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma check_lval_reg_callP r tt :
  check_lval_reg_call pmap r = ok tt ->
    (exists ii ty, r = Lnone ii ty) \/
    exists x,
      [/\ r = Lvar x, Mvar.get pmap.(locals) x = None & ~ Sv.In x pmap.(vnew)].
Proof.
  rewrite /check_lval_reg_call.
  case: r => //.
  + move=> ii ty _.
    by left; exists ii, ty.
  move=> x.
  case heq: get_local => [//|].
  t_xrbindP=> _ /check_diffP ? _.
  by right; exists x.
Qed.

Lemma get_LvarP r x :
  get_Lvar r = ok x ->
  r = Lvar x.
Proof. by case: r => //= _ [->]. Qed.

(* Another lemma on [set_sub_region].
   See [valid_state_set_move_regptr].
*)
Lemma valid_state_set_sub_region_regptr rmap m0 s1 s2 x sr ofs ty v p rmap2 :
  valid_state rmap m0 s1 s2 ->
  wf_sub_region sr x.(vtype) ->
  (forall zofs, ofs = Some zofs -> 0 <= zofs /\ zofs + size_of ty <= size_of x.(vtype)) ->
  get_local pmap x = Some (Pregptr p) ->
  set_sub_region rmap x sr ofs (size_of ty) = ok rmap2 ->
  eq_sub_region_val x.(vtype) (emem s2) sr (get_var_bytes rmap2 sr.(sr_region) x) v ->
  valid_state rmap2 m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v])
                       (with_vm s2 (evm s2).[p <- pof_val p.(vtype) (Vword (sub_region_addr sr))]).
Proof.
  move=> hvs hwf hofs hlx hset heqval.
  have /wf_locals /= hlocal := hlx.
  case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem.
  constructor=> //=.
  + rewrite get_var_neq //.
    by apply hlocal.(wfr_not_vrip).
  + rewrite get_var_neq //.
    by apply hlocal.(wfr_not_vrsp).
  + move=> y hget hnnew.
    rewrite get_var_neq; last by rewrite /get_local in hlx; congruence.
    rewrite get_var_neq; last by have := hlocal.(wfr_new); congruence.
    by apply heqvm.
  case: (hwfr) => hwfsr hval hptr; split.
  + apply (wfr_WF_set hwfsr hwf).
    by have [_ ->] := set_sub_regionP hset.
  + move=> y sry bytesy vy.
    move=> /(check_gvalid_set_sub_region hwf hset) [].
    + move=> [? ? <- ->]; subst x.
      rewrite get_gvar_eq //.
      case: heqval => hread hty'.
      apply on_vuP => //; rewrite -hty'.
      by move => ? hof hto; rewrite -hto (pto_val_pof_val hof) hty'.
    move=> [? [bytes [hgvalid ->]]].
    rewrite get_gvar_neq => // /(wfr_val hgvalid).
    assert (hwfy := check_gvalid_wf wfr_wf hgvalid).
    have hwf' := sub_region_at_ofs_wf hwf hofs.
    case: eqP => heqr /=.
    + by apply (eq_sub_region_val_same_region hwf' hwfy heqr).
    apply: (eq_sub_region_val_disjoint_regions hwf' hwfy heqr) => //.
    by case /set_sub_regionP : hset.
  move=> y sry.
  have /set_sub_regionP [_ ->] /= := hset.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists (Pregptr p); split=> //=.
    by rewrite get_var_eq hlocal.(wfr_rtype).
  move=> hneq /hptr [pk [hly hpk]].
  exists pk; split=> //.
  case: pk hly hpk => //=.
  + move=> py hly.
    have ? := hlocal.(wfr_distinct) hly hneq.
    by rewrite get_var_neq.
  move=> s osf ws z f hly hpk.
  rewrite /check_stack_ptr get_var_bytes_set_pure_bytes.
  case: eqP => [_|//].
  case: eqP => [heq|_].
  + have /wf_locals /wfs_new := hly.
    by have /wf_vnew := hlx; congruence.
  by move=> /mem_remove [] /hpk.
Qed.

(* TODO: we put ByteSet.full. Should we put get_var_bytes of a given rmap instead?
   Should not change anything, just a question of style.
   Or should we write get_val_byte -> read ... ?
*)
Definition R2 m (srs : seq (option (bool * sub_region) * pexpr)) i r v :=
  match i with
  | None => True
  | Some n =>
    exists x b sr e, [/\ r = Lvar x,
      nth (None, Pconst 0) srs n = (Some (b, sr), e),
      wf_sub_region sr x.(vtype) &
      eq_sub_region_val x.(vtype) m sr (ByteSet.full (interval_of_zone sr.(sr_zone))) v]
  end.

Lemma get_regptrP x p :
  get_regptr pmap x = ok p ->
  Mvar.get pmap.(locals) x = Some (Pregptr p).
Proof. by rewrite /get_regptr; case heq: get_local => [[]|] // [<-]. Qed.

Lemma alloc_lval_call rmap m0 s1 s2 srs r i rmap2 r2 v s1' :
  valid_state rmap m0 s1 s2 ->
  alloc_lval_call pmap srs rmap r i = ok (rmap2, r2) ->
  R2 (emem s2) srs i r v ->
  write_lval gd r v s1 = ok s1' ->
  exists v2 s2', [/\
    write_lval [::] r2 v2 s2 = ok s2',
    valid_state rmap2 m0 s1' s2' &
    Rout_aux (emem s2') i v v2].
Proof.
  move=> hvs halloc hr2 hw.
  move: halloc; rewrite /alloc_lval_call.
  case: i hr2 => [i|] hr2; last first.
  + t_xrbindP=> _ /check_lval_reg_callP hcheck <- <-.
    exists v.
    case: hcheck.
    + move=> [ii [ty ?]]; subst r.
      move: hw => /= /write_noneP [->] h; exists s2; split => //.
      by rewrite /write_none; case: h => [ [? ->]| [-> ->]].
    move=> [x [? hlx hnnew]]; subst r.
    move: hw; rewrite /= /write_var.
    t_xrbindP=> vm1 hvm1 <- /=.
    by apply: set_varP hvm1=> [v' hv <- | hb hv <-]; rewrite /set_var hv /= ?hb /=;
      eexists;(split;first by reflexivity) => //; apply valid_state_set_var.
  move: hr2 => [x [b [sr [e [? -> hwf heqval]]]]]; subst r => /=.
  t_xrbindP=> p /get_regptrP hlx {rmap2}rmap2 hset <- <-.
  have /wf_locals hlocal := hlx.
  move: hw; rewrite /= /write_var.
  t_xrbindP=> vm1 hvm1 <-.
  set v2 := Vword (sub_region_addr sr).
  set vp := pof_val p.(vtype) v2.
  have heq: forall off w, get_val_byte v off = ok w ->
    read (emem s2) (sub_region_addr sr + wrepr U64 off)%R U8 = ok w.
  + case: heqval => hread hty.
    move=> off w /dup[] /get_val_byte_bound; rewrite hty => hoff hget.
    apply hread => //.
    rewrite ByteSet.fullE /I.memi /= !zify.
    by have := hwf.(wfz_len); lia.
  exists v2, (with_vm s2 s2.(evm).[p <- vp]); split.
  + rewrite /vp /set_var.
    by case: (p) hlocal.(wfr_rtype) => -[??] ? /= ->.
  + set valid_state := valid_state. (* hack due to typeclass interacting badly *)
    apply: set_varP hvm1; last by have /is_sarrP [n {1}->] := hlocal.(wfr_type).
    move=> _ <- <-.
    apply: (valid_state_set_sub_region_regptr hvs hwf _ hlx hset).
    + by move=> _ [<-]; lia.
    case: heqval => hread hty.
    split=> //.
    by move=> off _ w; apply heq.
  by eexists; split; first by reflexivity.
Qed.

End Section.

Section INIT.

Variable global_data : seq u8.
Variable global_alloc : seq (var * wsize * Z).

Let glob_size := Z.of_nat (size global_data).

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
    + by apply Zland_mod.
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

Hypothesis hcheck : check_globs gd mglob global_data.

Lemma check_globP gd : check_glob mglob global_data gd ->
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
Lemma check_globsP : forall g, List.In g gd ->
  exists ofs ws,
    Mvar.get mglob g.1 = Some (ofs, ws) /\
    forall k w,
      get_val_byte (gv2val g.2) k = ok w ->
      nth 0%R global_data (Z.to_nat (ofs + k)) = w.
Proof.
  move: hcheck; rewrite /check_globs.
  elim: gd => // g gd ih /= /andP [/check_globP h1 /ih h2] ?.
  case; first by move <-.
  by apply h2.
Qed.

Section LOCAL.

Record wf_Slots (Slots : Sv.t) Addr (Writable:slot-> bool) Align := {
  wfsl_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s);
  wfsl_disjoint : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
    Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2);
  wfsl_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s)
}.
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
    + by apply Zland_mod.
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

Variables rip rsp : u64.
Hypothesis no_overflow_glob_size : no_overflow rip glob_size.
Hypothesis no_overflow_size : no_overflow rsp sao.(sao_size).
Hypothesis disjoint_zrange_globals_locals : disjoint_zrange rip glob_size rsp sao.(sao_size).
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

(* Lemma init_local_map
 *)
Definition param_pairs :=
  filter (fun xpi => isSome xpi.2) (zip (map v_var params) sao.(sao_params)).
Definition Slots_params := SvP.MP.of_list (map fst param_pairs).

Definition get_pi s :=
  let opi := assoc param_pairs s in
  match opi with
  | Some opi => opi
  | None => None
  end.

Hypothesis Addr_params : slot -> ptr.

Definition Writable_params s :=
  match get_pi s with
  | Some pi => pi.(pp_writable)
  | None    => false
  end.

Definition Align_params s :=
  match get_pi s with
  | Some pi => pi.(pp_align)
  | None    => U8
  end.

Hypothesis wf_Slots_params :
  wf_Slots Slots_params Addr_params Writable_params Align_params.
Hypothesis disjoint_zrange_globals_params :
  forall s, Sv.In s Slots_params -> Writable_params s ->
  disjoint_zrange rip glob_size (Addr_params s) (size_slot s).
Hypothesis disjoint_zrange_locals_params :
  forall s, Sv.In s Slots_params ->
  disjoint_zrange rsp sao.(sao_size) (Addr_params s) (size_slot s).


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
Lemma disjointP s1 s2 :
  reflect (forall x, Sv.In x s1 -> Sv.In x s2 -> False) (disjoint s1 s2).
Proof.
  case: (@idP (disjoint s1 s2)) => hdisj; constructor.
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

Variables vrip0 vrsp0 : var.
(* TODO: define sptr outside [Section] so that we can remove this duplicate. *)
Notation sptr := (sword Uptr) (only parsing).
Hypothesis wt_vrip0 : vrip0.(vtype) = sptr.
Hypothesis wt_vrsp0 : vrsp0.(vtype) = sptr.
Variable locals1 : Mvar.t ptr_kind.
Variable rmap1 : region_map.
Variable vnew1 : Sv.t.
Hypothesis hlocal_map : init_local_map vrip0 vrsp0 fn mglob stack sao = ok (locals1, rmap1, vnew1).
(* Variable params : seq var_i. *)
Variable vnew2 : Sv.t.
Variable locals2 : Mvar.t ptr_kind.
Variable rmap2 : region_map.
Variable alloc_params : seq (option region * var_i).
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

Lemma in_Slots_params s :
  Sv.In s Slots_params <-> exists x, x \in params /\ s = x.
Proof. (*
  rewrite SvP.MP.of_list_1 SetoidList.InA_alt.
  split.
  + move=> [_ [<-]].
    move=> /InP /mapP [x] ??.
    exists x. split=> //.
  move=> [x [h1 h2]].
  exists x. split=> //.
  apply /InP. apply /mapP. by exists x. *)
Abort.

Lemma uniq_param_pairs : uniq (map fst param_pairs).
Proof.
  have: uniq (map fst param_pairs) /\
    forall x, x \in map fst param_pairs -> Mvar.get locals1 x = None;
  last by move=> [].
  rewrite /param_pairs.
  move: hparams; rewrite /init_params.
  elim: params sao.(sao_params) vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params;
    first by move=> [].
  move=> x params' ih [//|opi sao_params].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' /=.
  case: opi => [pi|]; last first.
  + by move=> /=; t_xrbindP=> -[[[??]?]?] /ih.
  t_xrbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param'] _ _ _ _ _ _ _ _.
  case: Mvar.get => //.
  case: Mvar.get => //.
  case: Mvar.get => //.
  case heq: Mvar.get => //.
  move=> [_ ? _ _]; subst locals1'.
  move=> [[[_ _] _] _] /ih [ih1 ih2] _ _.
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

(* TODO: should param_info be declared eqType? so that we can use [\in]...
   For the current proof, we rely on the syntactic equality [filter = List.filter]... *)
Lemma in_Slots_params s :
  Sv.In s Slots_params <-> get_pi s <> None.
Proof.
  rewrite /Slots_params /get_pi SvP.MP.of_list_1 SetoidList.InA_alt.
  split.
  + move=> [] _ [<-] /InP /in_map [[x opi] hin ->].
    have -> := mem_uniq_assoc hin uniq_param_pairs.
    move: hin; rewrite /param_pairs.
    move=> /List.filter_In [] _.
    by case: opi.
  case heq: assoc => [opi|//] _.
  exists s; split=> //.
  apply /InP; apply /in_map.
  exists (s, opi) => //.
  by apply assoc_mem'.
Qed.

Lemma init_params_not_glob_nor_stack s pi :
  get_pi s = Some pi ->
  Mvar.get mglob s = None /\ Mvar.get stack s = None.
Proof.
  rewrite /get_pi /param_pairs.
  move: hparams; rewrite /init_params.
  elim: params sao.(sao_params) vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params;
    first by move=> [].
  move=> y params' ih  [//|opi2 sao_params].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' /=.
  case: opi2 => [pi2|]; last first.
  + by move=> /=; t_xrbindP=> -[[[??]?]?] /ih.
  t_xrbindP=> -[[[??]?]?] _ _ _ _ _ _ _ _.
  case: Mvar.get => //.
  case heq1: Mvar.get => //.
  case heq2: Mvar.get => //.
  case: Mvar.get => //.
  move=> _ [[[_ _] _] _] /ih{ih}ih _ _ /=.
  by case: eqP => [->|].
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

Lemma Hdisjoint_writable : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
  Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2).
Proof.
  move=> s1 s2 hin1 hin2 hneq hw.
  have hover1 := Haddr_no_overflow hin1.
  have hover2 := Haddr_no_overflow hin2.
  move /in_Slots : hin1 => [hin1|[hin1|hin1]].
  + by move: hw; rewrite /Writable (pick_slot_globals hin1).
  + move /in_Slots : hin2 => [hin2|[hin2|hin2]].
    + apply disjoint_zrange_sym.
      apply: disjoint_zrange_incl disjoint_zrange_globals_locals.
      + rewrite /Addr (pick_slot_globals hin2).
        by apply (zbetween_Addr_globals hin2).
      rewrite /Addr (pick_slot_locals hin1).
      by apply (zbetween_Addr_locals hin1).
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
    apply: disjoint_zrange_incl_l (disjoint_zrange_locals_params hin2).
    by apply (zbetween_Addr_locals hin1).
  move /in_Slots : hin2 => [hin2|[hin2|hin2]].
  + rewrite /Addr (pick_slot_params hin1) (pick_slot_globals hin2).
    rewrite /Writable (pick_slot_params hin1) in hw.
    apply disjoint_zrange_sym.
    apply: disjoint_zrange_incl_l (disjoint_zrange_globals_params hin1 hw).
    by apply (zbetween_Addr_globals hin2).
  + rewrite /Addr (pick_slot_params hin1) (pick_slot_locals hin2).
    apply disjoint_zrange_sym.
    apply: disjoint_zrange_incl_l (disjoint_zrange_locals_params hin1).
    by apply (zbetween_Addr_locals hin2).
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

Definition lmap locals' vnew' := {|
  vrip := vrip0;
  vrsp := vrsp0;
  globals := mglob;
  locals := locals';
  vnew := vnew'
|}.

Lemma add_alloc_wf locals1' rmap1' vnew1' x pki locals2' rmap2' vnew2' s1 s2:
  (forall y v, get_var s1.(evm) y = ok v -> y <> x) ->
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  wf_rmap (lmap locals1' vnew1') Slots Addr Writable Align P rmap1' s1 s2 ->
  add_alloc fn stack mglob (x, pki) (locals1', rmap1', vnew1') = ok (locals2', rmap2', vnew2') ->
  wf_pmap (lmap locals2' vnew2') rsp rip Slots Addr Writable Align /\
  wf_rmap (lmap locals2' vnew2') Slots Addr Writable Align P rmap2' s1 s2.
Proof.
  move=> hvm hpmap hrmap.
  case: (hpmap) => /= hrip hrsp hnew1 hnew2 hglobals hlocals hnew.
  case: (hrmap) => hwfsr hval hptr.
  case: Sv_memP => [//|hnnew].
  case hregx: Mvar.get => //.
  t_xrbindP=> {rmap2'} -[[sv pk] rmap2'] hpki [<- <- <-].
  case: pki hpki.
  + move=> s z sc.
    case heq: Mvar.get => [[ofs ws]|//].
    case: ifP => [/and3P []|//].
    rewrite !Zcmp_le !zify => h1 h2 h3 [<- <- <-].
    split.
    + split=> //=.
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
          by move=> /hvm.
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
      by have /hlocals /wfs_new /= := hly; congruence.
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
    split.
    + split=> //=.
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
  move=> h2 /eqP /(Zland_mod (ws:=U64)) h3 h4 h5 [<- <- <-].
  split.
  + split=> //=.
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
  split=> //.
  move=> y sry /hptr.
  rewrite /get_local /= => -[pky [hly hpky]].
  exists pky; split=> //.
  rewrite Mvar.setP.
  by case: eqP; first by congruence.
Qed.

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

(* TODO: clean *)
Lemma init_local_map_wf s1 s2 :
  (forall x v, get_var s1.(evm) x = ok v -> x = vrip0 \/ x = vrsp0) ->
(*   init_local_map vrip' vrsp' fn mglob sao = ok (locals', rmap, vnew') -> *)
  (forall i, 0 <= i < glob_size ->
    read (emem s2) (rip + wrepr U64 i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) ->
  wf_pmap (lmap locals1 vnew1) rsp rip Slots Addr Writable Align /\
  wf_rmap (lmap locals1 vnew1) Slots Addr Writable Align P rmap1 s1 s2.
Proof.
(*   move=> hgetg. *)
  move=> hget heqvalg.
  move: hlocal_map; rewrite init_local_map_eq /=.
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] hfold [???]; subst locals1' rmap1' vnew1'.
  move: hfold.
  have: wf_pmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).2) rsp rip
                      Slots Addr Writable Align
     /\ wf_rmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).2)
                Slots Addr Writable Align P (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).1.2 s1 s2
     /\ (forall x v, get_var s1.(evm) x = ok v -> Sv.In x (Mvar.empty ptr_kind, empty, Sv.add vrip0 (Sv.add vrsp0 Sv.empty)).2).
  + split.
    + split=> //=.
      + by apply SvD.F.add_1.
      + by apply SvD.F.add_2; apply SvD.F.add_1.
      by apply init_map_wf.
    split; last first.
    + move=> x v /hget [] ->.
      + apply Sv.add_spec. left. reflexivity.
      apply Sv.add_spec. right. apply Sv.add_spec. left. reflexivity.
    split=> //=.
    move=> y sry bytesy vy. rewrite /check_gvalid.
    case: ifP => // hg.
    rewrite /=. case heq: Mvar.get => [[ofs ws]|//] /=.
    move=> [<- <-]. rewrite get_gvar_glob //.
    move=> /get_globalI [gval [h1 h2 h3]].
    split=> //.
    move=> off _ w /dup[] /get_val_byte_bound H.
    have h := assoc_mem' h1.
    have := check_globsP h.
    rewrite heq.
    move=> [_ [_ [[<- _]]]] /=. rewrite -h2 => hh /hh <-.
    rewrite -heqvalg.
    rewrite /sub_region_addr /= /Addr pick_slot_globals /Addr_globals /Offset_slots.
    rewrite heq /=. rewrite wrepr0 GRing.addr0 wrepr_add GRing.addrA. done.
    apply in_Slots_slots. congruence.
    have ? := init_map_bounded heq. rewrite h3 in H. lia.
  elim: sao.(sao_alloc) (Mvar.empty _, _, _).
  + by move=> /= [[locals0 rmap0] vnew0] [?[??]] [<- <- <-].
  move=> [x pki] l ih [[locals0 rmap0] vnew0] /= hbase.
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] halloc.
  apply ih.
  apply and_assoc. split.
  apply and_assoc in hbase.
  apply: (add_alloc_wf _ hbase.1.1 hbase.1.2 halloc).
  move=> ?? /(hbase.2).
  case: Sv_memP halloc => // ? _. congruence.
  simpl.
  move: halloc.
  case: Sv.mem => //.
  case: Mvar.get => //.
  case: pki.
  + move=> s ofs sc. case: Mvar.get => [[ofs' ws]|//].
    case: ifP => // /=.
    move=> _ [_ _ <-]. move: hbase.2.2. done.
  + move=> p.
    case: ifP => // _.
    case: Sv.mem => //.
    case: Mvar.get => //.
    case: ifP => // _.
    move=> /= [_ _ <-].
    move=> ?? /hbase.2.2 ?. apply Sv.add_spec. right; done.
  move=> s ofs f.
  case: ifP => // _.
  case: Mvar.get => [[ofs' ws]|//].
  case: Sv.mem => //.
  case: eqP => // _.
  case: Mvar.get => //.
  case: ifP => //= _.
  move=> [_ _ <-].
  move=> ?? /hbase.2.2 ?. apply Sv.add_spec. right; done.
Qed.

(* proofs are very similar to add_alloc, can we factorize ? *)
(* TODO: should we prove valid_state instead of wf_rmap ?
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
    rewrite /Addr pick_slot_params. (* Rin ?? *) admit.
    apply in_Slots_params. congruence.
  move=> hneq /hptr [pky [hly hpky]].
  exists pky; split=> //.
  case: pky hly hpky => //= sy ofsy wsy zy yf hly hpky.
  rewrite /check_stack_ptr get_var_bytes_set_move_bytes /=.
  case: eqP => //=.
  case: eqP => //.
  by have /hlocals /wfs_new /= := hly; congruence.
Admitted.

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

Lemma get_pi_params :
  List.Forall2 (fun opi (x:var_i) => opi <> None -> get_pi x = opi) sao.(sao_params) params.
Proof.
  apply (Forall2_impl
    (R1:=fun opi (x:var_i) => opi <> None -> List.In (x.(v_var), opi) param_pairs)).
  + move=> opi x h /h{h}h.
    by rewrite /get_pi (mem_uniq_assoc h uniq_param_pairs).
  rewrite /param_pairs.
  move: hparams.
  elim: sao_params params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params.
  + by move=> [|//].
  move=> opi sao_params ih [//|x params'].
  rewrite /init_params /=.
  t_xrbindP=> _ _ _ _ _ _ _ -[[[_ _] _] _] _ [[[_ _] _] _] /ih{ih}ih _ _.
  constructor.
  + by case: opi => [pi|//] _ /=; left.
  apply: Forall2_impl ih.
  move=> opi' x' h /h.
  by case: opi => [pi|//] /= ?; right.
Qed.

Lemma init_params_wf s1 s2 :
  (forall x v, get_var s1.(evm) x = ok v -> x = vrip0 \/ x = vrsp0) ->
  (forall i, 0 <= i < glob_size ->
    read (emem s2) (rip + wrepr U64 i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) ->
  wf_pmap (lmap locals2 vnew2) rsp rip Slots Addr Writable Align /\
  wf_rmap (lmap locals2 vnew2) Slots Addr Writable Align P rmap2 s1 s2.
Proof.
  move=> hget heqvalg.
  move: hparams.
  have := init_local_map_wf hget heqvalg.
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
  Search _ write_var.
  rewrite /write_var.
  
  t_xrbindP=> s1' vm1.
  apply: set_varP.
  rewrite /set_var.

(* should we assume sth about valid_state ? or vm_uincl ? *)
Lemma test s1 s2 vargs1 vargs2 :
  Forall3 (Rin_aux (emem s2)) sao.(sao_params) vargs1 vargs2 ->
  forall s1', write_vars params vargs1 s1 = ok s1' ->
  exists s2',
  write_vars [seq i.2 | i <- alloc_params] vargs2 s2 = ok s2'.
Proof.
  move=> hin.
  move: hparams s1.
  elim: {vargs vargs'} hin params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params.
  + by move=> [|//] ??????? [_ _ _ <-]; exists s2.
  move=> opi varg varg' sao_params vargs vargs' hin1 hin2 ih.
  move=> [//|param params'] vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  t_xrbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  move=> [[[_ _] _]{alloc_params'}alloc_params'] /ih{ih}ih _ <- /=.
  move=> s1 s1'' s1' hs1' /ih ?.
  case: opi hin1 hparam => [pi|]; last first.
  + move=> -> [_ _ _ <-] /=.
    rewrite hs1'.
  alloc_lvalP
(*
  case: opi hin1 => [pi|] hin1.
  + 
  case: params => [//|param params'].
  case: opi hin1 => [pi|] hin1.
  rewrite /init_params /=.
  t_xrbindP. 
*)
Admitted.

End LOCAL.

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
    if sao.(sao_return_address) is RAnone then
      sao.(sao_size) + sao.(sao_extra_size) + wsize_size sao.(sao_align)
    else
      round_ws sao.(sao_align) (sao.(sao_size) + sao.(sao_extra_size))
  in
  allocatable_stack m (sao.(sao_max_size) - sz).

Record wf_sao rsp m sao := {
  wf_sao_size  : enough_size m sao;
  wf_sao_align : is_align rsp sao.(sao_align);
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

Variable rip : ptr. (* TODO: move *)

(* TODO: mettre sur 8 bits ? + no_overflow ? *)
Definition extend_mem (m1:mem) (m2:mem) (rip:ptr) (data: seq u8) :=
  let glob_size := Z.of_nat (size data) in
  [/\ wunsigned rip + glob_size <= wbase U64 /\
      (forall ofs s, is_align (rip + wrepr _ ofs)%R s = is_align (wrepr _ ofs) s), 
      (forall w sz, validw m1 w sz -> read m1 w sz = read m2 w sz),
      (forall w sz, validw m1 w sz -> (* disjoint_zrange rip glob_size w sz ? *)
          ~((wunsigned rip <? wunsigned w + wsize_size sz) && (wunsigned w <? wunsigned rip + glob_size))),
      (forall w sz, validw m2 w sz = 
         validw m1 w sz || (between rip glob_size w sz && is_align w sz)) &
      (forall i, 
         0 <= i < glob_size ->
         read m2 (rip + wrepr U64 i)%R U8 = ok (nth 0%R data (Z.to_nat i)))].

Let Pi_r s1 (i1:instr_r) s2 :=
  forall pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 ii1 ii2 i2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  alloc_i pmap local_alloc sao rmap1 (MkI ii1 i1) = ok (rmap2, MkI ii2 i2) ->
  forall s1', valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip P'.(p_extra).(sp_globs) ->
  wf_sao rsp (emem s1') sao ->
  exists s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' /\
              valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2' /\
              extend_mem (emem s2) (emem s2') rip P'.(p_extra).(sp_globs).

Let Pi s1 (i1:instr) s2 :=
  forall pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 i2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  alloc_i pmap local_alloc sao rmap1 i1 = ok (rmap2, i2) ->
  forall s1', valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip P'.(p_extra).(sp_globs) ->
  wf_sao rsp (emem s1') sao ->
  exists s2', sem_I (sCP:= sCP_stack) P' rip s1' i2 s2' /\
              valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2' /\
              extend_mem (emem s2) (emem s2') rip P'.(p_extra).(sp_globs).

(*
Let Pi_r s1 i1 s2 :=
  forall ii, Pi s1 (MkI ii i1) s2.
*)
(* voire Pi := Pc [:: i], mais sans doute surcout non négligeable *)

Let Pc s1 (c1:cmd) s2 :=
  forall pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 c2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  fmapM (alloc_i pmap local_alloc sao) rmap1 c1 = ok (rmap2, c2) ->
  forall s1', valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip P'.(p_extra).(sp_globs) ->
  wf_sao rsp (emem s1') sao ->
  exists s2', sem (sCP:= sCP_stack) P' rip s1' c2 s2' /\
              valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s2 s2' /\
              extend_mem (emem s2) (emem s2') rip P'.(p_extra).(sp_globs).

Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.


(*
Definition allocatable_stack (m : mem) (z : Z) :=
  (z <= wunsigned (top_stack m) - wunsigned (stack_limit m))%Z.
*)
(* TODO: edit allocatable_stack in low_memory *)
Definition alloc_ok (SP:sprog) fn m2 :=
  forall fd, get_fundef (p_funcs SP) fn = Some fd ->
  allocatable_stack m2 fd.(f_extra).(sf_stk_max).

(* Addr ??? *)
Definition Rin m fn :=
  Forall3 (Rin_aux m) (local_alloc fn).(sao_params).
Definition Rout m fn :=
  Forall3 (Rout_aux m) (local_alloc fn).(sao_return).

Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) :=
  forall m1' vargs',
    extend_mem m1 m1' rip P'.(p_extra).(sp_globs) ->
    Rin m1' fn vargs vargs' ->
    alloc_ok P' fn m1' ->
    exists m2' vres',
      List.Forall2 value_uincl vres vres' /\
      extend_mem m2 m2' rip P'.(p_extra).(sp_globs) /\
      Rout m2' fn vres vres' /\
      sem_call (sCP := sCP_stack) P' rip m1' fn vargs' m2' vres'.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 /= c2 hpmap hwf sao [??] s' hv hext hsao;subst rmap1 c2.
  exists s'; split => //; exact: Eskip. 
Qed.

Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc pmap rsp Slots Addr Writable Align m0 rmap1 rmap3 c1 hpmap hwf sao /=.
  t_xrbindP => -[rmap2 i'] hi {rmap3} [rmap3 c'] hc /= <- <- s1' hv hext hsao.
  have [s2' [si [hv2 hext2]]]:= Hi _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hi _ hv hext hsao.
  have hsao2 := stack_stable_wf_sao (sem_I_stack_stable si) hsao.
  have [s3' [sc [hv3 hext3]]]:= Hc _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc _ hv2 hext2 hsao2.
  by exists s3'; split => //; apply: Eseq; [exact: si|exact: sc].
Qed.

Local Lemma HmkI : sem_Ind_mkI P ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 [ii' ir'] hpmap hwf sao ha s1' hv hext hsao.
  by have [s2' [Hs2'1 [Hs2'2 Hs2'3]]] := Hi _ _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ ha _ hv hext hsao; exists s2'; split.
Qed.

Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
Proof.
  move=> s1 s1' r tag ty e v v' hv htr hw pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap2' i2'] h /= ??? s2 hvs hext hsao; subst rmap2' ii1 i2'.
  case: ifPn h => [/is_sarrP [n ?]| _ ].
  + subst ty; apply: add_iinfoP.
(*     by apply (alloc_array_move_initP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap P'_globs hvs hv htr hw). *)
    admit.
  t_xrbindP => e'; apply: add_iinfoP => /(alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs) he [rmap2' x'].
  apply: add_iinfoP => hax /= ??; subst rmap2' i2.
  have htyv':= truncate_val_has_type htr.
  have [s2' [/= hw' hvs']]:= alloc_lvalP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap hax hvs htyv' hw.
  exists s2';split => //.
  by apply: Eassgn; eauto; rewrite P'_globs; auto.
  split=> //.
  admit.
Admitted.

Local Lemma Hopn : sem_Ind_opn P Pi_r.
Proof.
  move=> s1 s2 t o xs es.
  rewrite /sem_sopn; t_xrbindP=> vs va hes hop hw pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP=> -[rmap3 i'] es'; apply: add_iinfoP => he [rmap4 x'];
    apply: add_iinfoP => ha /= [<- <-] <- _ <- s1' hvs hext hsao.
  have [s2' [hw' hvalid']] := alloc_lvalsP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap ha hvs (sopn_toutP hop) hw.
  exists s2'; split=> //.
  constructor.
  by rewrite /sem_sopn P'_globs (alloc_esP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs he hes) /= hop.
  split=> //.
  admit.
Admitted.

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
  valid_state pmap rsp rip Slots Addr Writable Align P rmap2 m0 s s' ->
  valid_state pmap rsp rip Slots Addr Writable Align P rmap1 m0 s s'.
Proof.
  move=> hincl hvs.
  case:(hvs) => hvalid hdisj hvincl hunch hrip hrsp heqvm hwfr heqmem.
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
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] e'; apply: add_iinfoP => he [rmap4 c1'] hc1 [rmap5 c2'] hc2 /= [??]??? s1' hv hext hsao.
  subst rmap3 i' rmap2 ii1 i2.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv he Hse; rewrite -P'_globs => he'.
  have [s2' [Hsem [Hvalid' Hext']]] := Hc _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ hv hext hsao.
  exists s2'; split; first by apply: Eif_true.
  split=> //.
  by apply: valid_state_incl Hvalid'; apply incl_merge_l.
Qed.

Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] e'; apply: add_iinfoP => he [rmap4 c1'] hc1 [rmap5 c2'] hc2 /= [??]??? s1' hv hext hsao.
  subst rmap3 i' rmap2 ii1 i2.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv he Hse; rewrite -P'_globs => he'.
  have [s2' [Hsem [Hvalid' Hext']]] := Hc _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ hv hext hsao.
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
  move=> s1 s2 s3 s4 a c1 e c2 _ Hc1 Hv _ Hc2 _ Hwhile pmap rsp Slots Addr Writable Align m0
    rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] [rmap4 [e' [c1' c2']]] /loop2P [rmap5 [rmap6 [hincl1 []]]].
  t_xrbindP => -[rmap7 c11] hc1 /= e1; apply: add_iinfoP => he [rmap8 c22] /= hc2 ????? hincl2 [??]???.
  subst i2 ii1 rmap3 rmap4 i' rmap7 rmap8 e1 c11 c22 => s1' /(valid_state_incl hincl1) hv hext hsao.
  have [s2' [hs1 [hv2 hext2]]]:= Hc1 _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ hv hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv2 he Hv; rewrite -P'_globs => he'.
  have hsao2 := stack_stable_wf_sao (sem_stack_stable hs1) hsao.
  have [s3' [hs2 [/(valid_state_incl hincl2) hv3 hext3]]]:= Hc2 _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ hv2 hext2 hsao2.
  have /= := Hwhile _ _ _ _ _ _ m0 rmap5 rmap2 ii2 ii2 (Cwhile a c1' e' c2') hpmap hwf sao.
  have hsao3 := stack_stable_wf_sao (sem_stack_stable hs2) hsao2.
  rewrite Loop.nbP /= hc1 /= he /= hc2 /= hincl2 /= => /(_ erefl _ hv3 hext3 hsao3) [s4'] [hs3 hv4].
  by exists s4';split => //; apply: Ewhile_true; eassumption.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 a c1 e c2 _ Hc1 Hv pmap rsp Slots Addr Writable Align m0 rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP => -[rmap3 i'] [rmap4 [e' [c1' c2']]] /loop2P [rmap5 [rmap6 [hincl1 []]]].
  t_xrbindP => -[rmap7 c11] hc1 /= e1; apply: add_iinfoP => he [rmap8 c22] /= hc2 ????? hincl2 [??]???.
  subst i2 ii1 rmap3 rmap4 i' rmap7 rmap8 e1 c11 c22 => s1' /(valid_state_incl hincl1) hv hext hsao.
  have [s2' [hs1 [hv2 hext2]]]:= Hc1 _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ hv hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hv2 he Hv; rewrite -P'_globs => he'.
  by exists s2';split => //; apply: Ewhile_false; eassumption.
Qed.

Local Lemma Hfor : sem_Ind_for P ev Pi_r Pfor.
Proof. by []. Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by []. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons P ev Pc Pfor.
Proof. by []. Qed.

Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
Proof.
  move=> s1 m2 s2 ii xs fn args vargs vs hargs _ Hf hw pmap rsp Slots Addr Writable Align
    m0 rmap1 rmap2 ii1 ii2 i2 hpmap hwf sao /=.
  t_xrbindP=> -[rmap3 i3]; apply: add_iinfoP => /= hc ??? s3 hvs hext hsao; subst rmap3 ii2 i3.
  move: hc.
  rewrite /alloc_call.
  t_xrbindP => es hes [rmap3 rs] hrs _ /assertP /ZleP hsize /= ??; subst rmap3 i2.
  have [vargs' [hvargs' hRin]]:= alloc_call_argsP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs hes hargs.
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
  have halloc: alloc_ok P' fn (emem s3).
  + move=> fd hfd.
    move: hsao.(wf_sao_size).
    rewrite /enough_size.
    rewrite /allocatable_stack.
    have H: sf_stk_max fd.(f_extra) = (local_alloc fn).(sao_max_size).
    + admit.
    rewrite H.
    case: sao_return_address.
    + move=> h. apply: Z.le_trans; last by apply h.
      admit.
    + admit.
    admit.

  have [m2' [vres' [H1 [H2 [H3 H4]]]]] := Hf _ _ hext hRin halloc.
  eexists; split.
  econstructor.
  rewrite P'_globs. eassumption.
  eassumption.
  admit. (*
  eassumption.
  rewrite /Pfun in Hf.
  apply H4.
  *)
Admitted.

Lemma add_err_funP A (a:A) (e:cexec A) P0 fn :
  (e = ok a -> P0) -> add_err_fun fn e = ok a -> P0.
Proof.
  case: e => //= a' h [?]; subst a'.
  by apply h.
Qed.

(*
Lemma alloc_funP_eq_aux fn f f' m1 m2 vargs vargs' vres s0 s1 s2 vres':
get_fundef (p_funcs P) fn = Some f ->
get_fundef (p_funcs P') fn = Some f' ->
(*       alloc_fd P'.(p_extra)  ep1 ep2 (fn, f) (fn, f') tt = ok tt -> *)
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) P.(p_extra) ev (Estate m1 vmap0) = ok s0 ->
      write_vars (f_params f) vargs s0 = ok s1 ->
      sem P ev s1 (f_body f) s2 ->
      mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) P'.(p_extra) rip (Estate m1 vmap0) = ok (with_vm s0 vm0') /\
            write_vars (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem P' rip (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ mapM (fun x : var_i => get_var (evm (with_vm s2 vm2')) x) (f_res f') = ok vres1, 
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            m2 = finalize f'.(f_extra) s2.(emem) ].
    Proof.
      move=> /Halloc_fd [f'' [hf' halloc]].
      rewrite hf' => -[?]; subst f''.
      move=> hvargs hinit hw hsem hvres htr hfinalize.
      move: halloc.
      rewrite /alloc_fd /alloc_fd_aux.
      t_xrbindP=> /= f'' [[locals1 rmap1] vnew1] hinit2.
      t_xrbindP=> -[[[vnew2 locals2] rmap2] es].
      apply: add_err_funP.
      move=> hinitp.
      t_xrbindP=> -[rmap3 c].
      apply: add_finfoP.
      move=> halloc_i.
      t_xrbindP=> eres.
      apply: add_err_funP.
      move=> hcheck.
      move=> ??; subst f'' f'. (*
      eexists _, _, _, _, _.
      split.
      + simpl. move: hinitp hvargs. move: hvargs.
      elim: vargs' f.(f_tyin) (sao_params (local_alloc fn)).
      + move=> [] [] //.
      move=> a vargs' ih [] //= i ty_in.
      move=> [] /=. admit.
      move=> sao sao_params.
      t_xrbindP=> v1 htr1 v1s htr1s <-.
      t_xrbindP.
      +  case: f.(f_tyin) => //= [<-].
        case: (sao_params (local_alloc fn)) => //.
      rewrite /=.
      t_xrbindP. /alloc_fd_aux.
      case: ifP => // /andP[]/andP[]/eqP htyin /eqP htyout /eqP hextra;apply: add_finfoP.
      apply:rbindP => r0; apply: add_iinfoP => Hcinit.
      apply:rbindP => r1;apply:add_iinfoP => Hcparams.
      apply:rbindP => r2 Hcc;apply: rbindP => r3;apply: add_iinfoP => Hcres _ Hca.
      move=> /(init_allocP Hcinit) [vm0 [Hi0 Hvm0]].
      rewrite (write_vars_lvals gd)=> /(check_lvalsP Hcparams).
      move=> /(_ vargs _ Hvm0) [ | vm3 /= [Hw2 Hvm3]].
      + by apply: List_Forall2_refl.
      move=> /(sem_Ind Hskip Hcons HmkI Hassgn Hopn Hif_true Hif_false
                Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc_eq) Hc.
      have [vm4 /= [Hvm4 Hsc2] Hres Hcr]:= Hc _ _ _ _ _ Hvm3 Hcc.
      have := check_esP Hcres Hvm4.
      move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres1' /= []].
      rewrite sem_pexprs_get_var => hmap huincl ?.
      have [vres2' ??]:= mapM2_truncate_val Hcr huincl.
      do 5 eexists;split;eauto.
      + by rewrite -htyin.
      + split;eauto.
        by rewrite (write_vars_lvals gd).
      + by rewrite -htyout;split;eauto.
      by rewrite -hextra. *)
Abort. *)

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

Lemma truncate_val_get_val_byte ty v v' :
  truncate_val ty v = ok v' ->
  forall off w,
    get_val_byte v' off = ok w ->
    get_val_byte v off = ok w.
Proof.
  rewrite /truncate_val; t_xrbindP.
  case: ty => /=.
  + by move=> b _ <-.
  + by move=> z _ <-.
  + move=> len a /to_arrI [len' [a' [-> hcast]]] <-.
    move=> off w.
    by apply (cast_get8 hcast).
  move=> ws w /to_wordI [ws' [w' [hle -> ->]]] <-.
  move=> off w'' /=.
  case: ifP => //; rewrite !zify => hoff.
  have hle' := wsize_size_le hle.
  case: ifPn => [_|]; last by rewrite !zify; lia.
  move=> <-; f_equal; symmetry.
  by apply zero_extend_wread8.
Qed.

Lemma mapM2_truncate_val_Rin m fn vargs vargs2 tyin :
  mapM2 ErrType truncate_val tyin vargs = ok vargs2 ->
  forall vargs',
    Rin m fn vargs vargs' ->
    exists vargs2',
      mapM2 ErrType truncate_val
          (map2 (fun o ty =>
            match o with
            | Some _ => sword64
            | None => ty
            end) (sao_params (local_alloc fn)) tyin) vargs' = ok vargs2' /\
      Rin m fn vargs2 vargs2'.
Proof.
  rewrite /Rin.
  move=> htr vargs' hin.
  elim: {vargs vargs'} hin tyin vargs2 htr.
  + move=> [|//] /= _ [<-].
    eexists; split; first by reflexivity.
    by constructor.
  move=> [pi|] varg varg' sao_params vargs vargs' hin1 hin2 ih [//|ty tyin] vargs2 htr.
  + move: hin1 => [p [-> [hal hread]]].
    move: htr => /=; t_xrbindP=> varg2 htr {vargs2}vargs2 /ih [vargs2' [-> hin']] <-.
    eexists; split; first by reflexivity.
    constructor => //.
    rewrite zero_extend_u.
    eexists; split; first by reflexivity.
    split=> //.
    by move=> off w /(truncate_val_get_val_byte htr); apply hread.
  move: hin1 => /= ->.
  move: htr => /=; t_xrbindP=> varg2 -> {vargs2}vargs2 /ih [vargs2' [-> hin']] <-.
  eexists; split; first by reflexivity.
  by constructor.
Qed.

(* questions pour Benjamin :
   - vargs : quand on met un registre ?
   - quoi mettre dans allocatable_stack / check dans stack_alloc ?
   - live range splitting sur un exemple
*)
Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
Proof.
  move=> m1 _ fn fd vargs1 vargs2 _ s1 s2 vres1 vres2 hfd hvargs /= [<-] hs1 _ Hc hvres hvres' ->.
  move=> m1' vargs2' hext hin hok.
  have [fd' [] hfd'] := Halloc_fd hfd.
  rewrite /alloc_fd /=.
  t_xrbindP=> fd'' stack hlayout [[locals1 rmap1] vnew1] hlocal_map.
  t_xrbindP=> -[[[vnew2 locals2] rmap2] alloc_params].
  apply: add_err_funP => hparams.
  t_xrbindP=> -[rmap3 c].
  apply: add_finfoP => halloc.
  t_xrbindP=> res.
  apply: add_err_funP.
  move=> hresults ??; subst fd''.
  have: exists vargs1', mapM2 ErrType truncate_val (f_tyin fd') vargs2' = ok vargs1'.
  + subst fd' => /=. move: hvargs.
  (*   rewrite /Rin in hin. *)
    elim: hin fd.(f_tyin) (vargs1).
    + move=> tyin vargs1'''. simpl. move=> _. eexists; reflexivity.
    move=> opi v1 v2 sao_params vargs11 vargs22.
    move=> h.
    move=> h2.
    move=> ih.
    move=> [//|ty tyin] vargs1''' /=.
    t_xrbindP=> v1' hv1' vargs12 hvargs12 ?.
    case: opi h => [pi|]; last first.
    + move=> ->. rewrite hv1' /=.
      have [vargs1' ->] := ih _ _ hvargs12.
      rewrite /=. eexists; reflexivity.
    move=> [p [hp [hal hoff]]].
    rewrite hp /=.
    have [vargs1' ->] := ih _ _ hvargs12.
    rewrite /=. eexists; reflexivity.
  move=> [vargs1' hvargs1'].
  have := @Memory.alloc_stack_complete m1' (sao_align (local_alloc fn))
                                           (sao_size (local_alloc fn))
                                           (sao_extra_size (local_alloc fn)).
  move=> [].
  + apply /and3P.
    split.
    + (* true *) apply /ZleP. by apply (init_stack_layout_size_ge0 hlayout).
    + (* missing check? *) admit.
    move: hok. rewrite /alloc_ok => /(_ _ hfd').
    rewrite /allocatable_stack. subst fd' =>/=.
    (* wf_sao ?? *) admit.
  move=> m2' halloc_stk.

  have H: forall s, exists s',
    write_vars (f_params fd') vargs1' s = ok s'.
  + subst fd'. simpl. simpl in hvargs1'. move=> s. rewrite /write_vars.
    admit.

  eexists _, _.
  split; last split; last split; last first.
  econstructor.
  eassumption.
  eassumption.
  rewrite /= /init_stk_state /=.
  rewrite /with_vm /=.
  subst fd' => /=. rewrite halloc_stk /=.
  reflexivity.
  Search _ (vmap -> vmap -> Prop). eq_vm
  rewrite /Pc in Hc.
  have := Hc _ _ _ _ _ _ _ _ _ _ _ _ _ halloc.
  have := init_params_wf
  
  
  write_vars
  rewrite Fv.set.
  admit.
  apply Hc.
  rewrite /write_vars /=.
  rewrite /=.
  sem_call
  truncate_val
  
  
  have := hinit.
  rewrite /init_local_map.
  t_xrbindP=> -[??] hlayout _.
  have := init_local_map_wf hlayout _ _ _ _ _ _ _ hinit.
  move=> /(_ refl_equal refl_equal (top_stack m1')).
  have hal: is_align (top_stack m1') (sao_align (local_alloc fn)).
  + admit.
  move=> /(_ hal) h1.
  have := @Memory.alloc_stack_complete m1' (sao_align (local_alloc fn))
                                           (sao_size (local_alloc fn))
                                           (sao_extra_size (local_alloc fn)).
  move=> [].
  + apply /and3P.
    split.
    + (* true *) admit.
    + (* missing check? *) admit.
    rewrite hal. (* missing check *)
    admit.
  move=> m2' hstack.
  exists m2'. eexists; split.
  admit.
  split.
  + admit.
  apply: (EcallRun hfd'). alloc_call_arg
  admit.
  rewrite /= /init_stk_state.
  rewrite /= in hstack.
  subst fd'. rewrite /=. rewrite hstack /=. reflexivity.
  rewrite /write_vars /=.
  simpl. reflexivity.
  Search _ (with_vm (with_vm _ _) _). write_var set_var
  rewrite !with_vm_idem /with_vm /=.
  admit.
    admit.
    admit.
    Search _ is_align frames. mkASS
    extend_mem top_stack frames
  
  have := hok _ hfd'.
  rewrite /allocatable_stack /=. ring_simplify (wunsigned (stack_root m1') - wunsigned (stack_limit m1') -
   (wunsigned (stack_root m1') - wunsigned (top_stack m1'))).
  admit.
  movetop_stack alloc_stack_spec
  rewrite /Pc in Hc.
  init_params
  extend_mem
  Hslot_align
Admitted.

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
*)

(* R et Rout: liens entre les valeurs avant et après stack_alloc.
   R ty_in va va': va' = va si None et reg ptr (pointe vers une zone dans laquelle il y a va)
   et si reg ptr est writable, il doit être disjoint de tous les autres trucs
   et dans la pile

   Rout peut-être qu'on a besoin de prendre va' en argument pour dire que vr' = va'
   (en tout cas même région) dans le cas reg ptr
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
