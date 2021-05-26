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

(* Size of a value. *)
Notation size_val v := (size_of (type_of_val v)).

(* TODO : move elsewhere *)
(* but not clear where
   Uptr is defined in memory_model, no stype there
   stype is defined in type, no Uptr there
*)
Notation sptr := (sword Uptr) (only parsing).

Section Section.

(* TODO: remove stk_size *)
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

Hypothesis writable_not_glob : forall s, Sv.In s Slots -> Writable s ->
  0 < glob_size -> disjoint_zrange rip glob_size (Addr s) (size_slot s).

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
  vs_eq_mem     : eq_mem_source s1.(emem) s2.(emem);
  vs_glob_valid : forall p, between rip glob_size p U8 -> validw m0 p U8;
  vs_top_stack  : rsp = top_stack (emem s2);
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

  Lemma Zland_mod z ws : Z.land z (wsize_size ws - 1) = z mod wsize_size ws.
  Proof.
    rewrite wsize_size_is_pow2 -Z.land_ones; last by case: ws.
    by rewrite Z.ones_equiv.
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
    by apply /is_align_mod; rewrite -Zland_mod (slot_wrepr hwf).
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
  case: s1 s2 => mem1 vm1 [mem2 vm2] [/=] hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem hglobv htop hget hnin.
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
  stack_stable (emem s2) mem2 ->
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
  move=> hvs hwf hlx hpk hofs hss hvalideq hreadeq hset heqval.
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
  + by apply (eq_mem_source_write_slot hvs hwf' hreadeq).
  by rewrite -hss.(ss_top_stack).
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
    apply: (valid_state_set_sub_region hvs hwf hlx hpk hofs' _ _ _ hset (v:=Vword (zero_extend ws w'))).
    + by apply (Memory.write_mem_stable hmem2).
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
    case:(hvs) => hvalid hdisj hincl hunch hrip hrsp heqvm hwfr heqmem hglobv htop.
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
    by rewrite -(Memory.write_mem_stable hmem2).(ss_top_stack).

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
  apply: (valid_state_set_sub_region hvs hwf hlx hpk hofs' _ hvalideq _ hset (v:=Varr t')).
  + by apply (Memory.write_mem_stable hmem2).
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
  stack_stable (emem s2) mem2 ->
  (forall p ws,
    validw mem2 p ws = validw (emem s2) p ws) ->
  (forall p ws,
    disjoint_range (sub_region_addr (sub_region_stkptr s ws z)) Uptr p ws ->
    read mem2 p ws = read (emem s2) p ws) ->
  read mem2 (sub_region_addr (sub_region_stkptr s ws z)) U64 = ok (sub_region_addr sr) ->
  eq_sub_region_val x.(vtype) (emem s2) sr (get_var_bytes (set_move rmap x sr) sr.(sr_region) x) v ->
  valid_state (set_stack_ptr (set_move rmap x sr) s ws z f) m0 (with_vm s1 (evm s1).[x <- pof_val x.(vtype) v]) (with_mem s2 mem2).
Proof.
  move=> hvs hwf hlx hss hvalideq hreadeq hreadptr heqval.
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
  + by apply (eq_mem_source_write_slot hvs hwfs hreadeq).
  by rewrite -hss.(ss_top_stack).
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

    have {hi2} [mem2 [hsemi hss hvalideq hreadeq hreadptr]]:
      exists mem2,
      [/\ sem_i P' rip s2 i2 (with_mem s2 mem2),
          stack_stable (emem s2) mem2,
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
      + by apply (Memory.write_mem_stable hmem2).
      + by move=> ??; apply (write_validw_eq hmem2).
      + by move=> ??; apply (writeP_neq hmem2).
      rewrite (writeP_eq hmem2).
      by rewrite wrepr_add GRing.addrA -haddr -sub_region_addr_offset.

    exists (with_mem s2 mem2); split=> //.
    by apply (valid_state_set_stack_ptr hvs hwf hlx hss hvalideq hreadeq hreadptr (heqval _)).

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

Record wf_arg_pointer m1 m2 pi va p := {
  wap_align             : is_align p pi.(pp_align);
  wap_no_overflow       : no_overflow p (size_val va);
  wap_valid             : forall w, between p (size_val va) w U8 -> validw m2 w U8;
  wap_fresh             : forall w, validw m1 w U8 -> disjoint_zrange p (size_val va) w (wsize_size U8);
  wap_writable_not_glob : pi.(pp_writable) -> 0 < glob_size -> disjoint_zrange rip glob_size p (size_val va);
  wap_read              : forall off w, get_val_byte va off = ok w -> read m2 (p + wrepr _ off)%R U8 = ok w
}.

(* Rin: link between the values given as arguments in the source and the target. *)
Definition wf_arg m1 m2 sao_param va va' :=
  match sao_param with
  | None => va' = va
  | Some pi =>
    exists p,
      va' = Vword p /\ wf_arg_pointer m1 m2 pi va p
  end.

(* TODO: move to stack_alloc_proof_2? *)
Definition disjoint_values (sao_params:seq (option param_info)) va va' :=
  forall i1 pi1 w1 i2 pi2 w2,
    nth None sao_params i1 = Some pi1 ->
    nth (Vbool true) va' i1 = @Vword Uptr w1 ->
    nth None sao_params i2 = Some pi2 ->
    nth (Vbool true) va' i2 = @Vword Uptr w2 ->
    i1 <> i2 -> pi1.(pp_writable) ->
    disjoint_zrange w1 (size_val (nth (Vbool true) va i1)) w2 (size_val (nth (Vbool true) va i2)).

Record wf_result_pointer m1 vargs1 vargs2 i vr p := {
  wrp_args : nth (Vbool true) vargs2 i = Vword p;
  wrp_size : size_val vr <= size_val (nth (Vbool true) vargs1 i);
  wrp_read : forall off w, get_val_byte vr off = ok w -> read m1 (p + wrepr _ off)%R U8 = ok w
}.

(* Rout: link between the values returned by the function in the source and the target. *)
Definition wf_result m1 vargs1 vargs2 (i : option nat) vr vr' :=
  match i with
  | None => vr' = vr
  | Some i =>
    exists p, vr' = Vword p /\ wf_result_pointer m1 vargs1 vargs2 i vr p
  end.

Lemma get_PvarP e x : get_Pvar e = ok x -> e = Pvar x.
Proof. by case: e => //= _ [->]. Qed.

Lemma zbetween_le p sz1 sz2 :
  sz2 <= sz1 ->
  zbetween p sz1 p sz2.
Proof. by rewrite /zbetween !zify; lia. Qed.

Lemma alloc_call_argP m0 rmap s1 s2 sao_param e v osr e' :
  valid_state rmap m0 s1 s2 ->
  alloc_call_arg pmap rmap sao_param e = ok (osr, e') ->
  sem_pexpr gd s1 e = ok v ->
  exists v',
    sem_pexpr [::] s2 e' = ok v' /\
    wf_arg (emem s1) (emem s2) sao_param v v' /\
    (sao_param <> None -> osr <> None) /\
    forall b sr, osr = Some (b, sr) -> v' = Vword (sub_region_addr sr) /\ wf_sub_region sr (type_of_val v). (*
    exists x, e = Pvar x /\ ~ is_glob x /\
    forall b sr, osr = Some (b, sr) ->
      wf_sub_region sr x.(gv).(vtype) /\
      eq_sub_region_val x.(gv).(vtype) (emem s2) sr (ByteSet.full (interval_of_zone sr.(sr_zone))) v. *)
Proof.
  move=> hvs.
  rewrite /alloc_call_arg.
  t_xrbindP=> x /get_PvarP -> _ /assertP.
  case: x => x [] //= _.
  case: sao_param => [pi|]; last first.
  + case hlx: get_local => //.
    t_xrbindP=> _ /check_diffP hnnew <- <- /= hget.
    have hkind: get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    have hget2 := get_var_kindP hvs hkind hnnew hget.
    by exists v.
  case hlx: get_local => [pk|//].
  case: pk hlx => // p hlx.
  t_xrbindP=> -[sr _] /check_validP [bytes [hgvalid -> hmem]] ? hwritable.
  assert (hwf := check_gvalid_wf wfr_wf hgvalid); move=> /= in hwf.
  move=> _ /(check_alignP hwf) halign <- <- /= hget.
  have /wfr_gptr := hgvalid.
  rewrite /get_var_kind /= hlx => -[_ [[<-] /=]].
  rewrite get_gvar_nglob // => ->.
  eexists; split; first by reflexivity.
  split. {
  eexists; split; first by reflexivity.
  have /= hle := size_of_le (type_of_get_gvar hget).
  split.
  + by apply halign.
  + have /= := no_overflow_sub_region_addr hwf.
    apply no_overflow_incl.
    by apply: zbetween_le hle.
  + move=> w hb.
    apply (vs_slot_valid hwf.(wfr_slot)).
    apply (zbetween_trans (zbetween_sub_region_addr hwf)).
    apply: zbetween_trans hb.
    by apply: zbetween_le hle.
  + move=> w hvalid.
    apply: disjoint_zrange_incl_l (vs_disjoint hwf.(wfr_slot) hvalid).
    apply (zbetween_trans (zbetween_sub_region_addr hwf)).
    by apply: zbetween_le hle.
  + move=> hw hgsize.
    move: hwritable; rewrite hw /= => /assertP => hwritable.
    apply: disjoint_zrange_incl_r (writable_not_glob hwf.(wfr_slot) _ hgsize);
      last by rewrite hwf.(wfr_writable).
    apply: (zbetween_trans (zbetween_sub_region_addr hwf)).
    by apply: zbetween_le hle.
  move=> off w /dup[] /get_val_byte_bound hbound.
  assert (hval := wfr_val hgvalid hget).
  case: hval => hread hty.
  rewrite hty in hbound.
  apply hread.
  rewrite memi_mem_U8; apply: subset_mem hmem; rewrite subset_interval_of_zone.
  rewrite -(Z.add_0_l off).
  rewrite -(sub_zone_at_ofs_compose _ _ _ (size_slot x)).
  apply zbetween_zone_byte => //.
  by apply zbetween_zone_refl. }
  split=> //.
  move=> _ _ [_ <-].
  split=> //.
  apply: wf_sub_region_subtype hwf.
  by apply (type_of_get_gvar hget).
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
    Forall3 (wf_arg (emem s1) (emem s2)) sao_params vargs vargs' /\
    List.Forall2 (fun opi '(bsr, _) => opi <> None -> bsr <> None) sao_params l /\
    Forall3 (fun '(bsr, _) varg varg' => forall b sr, bsr = Some (b, sr) ->
      varg' = Vword (sub_region_addr sr) /\ wf_sub_region sr (type_of_val varg)) l vargs vargs'.
(*     Forall (fun '(osr, _) => match osr with ..) *)
Proof.
  move=> hvs.
  rewrite /alloc_call_args.
  t_xrbindP=> {l}l hmap _ _ <-.
  elim: sao_params args l vargs hmap.
  + move=> [|//] /= _ _ [<-] [<-].
    eexists; split; first by reflexivity.
    split; first by constructor.
    by split; constructor.
  move=> pi sao_params ih [//|arg args] l' vargs /=.
  t_xrbindP=> -[osr e] halloc l hmap ? varg hvarg vargs' hvargs' ?; subst l' vargs.
  rewrite /=.
  have [varg' [hvarg' [hin1 [hin2 hin3]]]] := (alloc_call_argP hvs halloc hvarg).
  have [vargs'' [hvargs'' [hin' [hin'2 hin'3]]]] := ih _ _ _ hmap hvargs'.
  rewrite hvarg' hvargs'' /=.
  eexists; split; first by reflexivity.
  split.
  + by constructor.
  by split; constructor.
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

Lemma get_regptrP x p :
  get_regptr pmap x = ok p ->
  Mvar.get pmap.(locals) x = Some (Pregptr p).
Proof. by rewrite /get_regptr; case heq: get_local => [[]|] // [<-]. Qed.

Lemma alloc_lval_callP rmap m0 s1 s2 srs r i rmap2 r2 v s1' :
  valid_state rmap m0 s1 s2 ->
  alloc_lval_call pmap srs rmap r i = ok (rmap2, r2) ->
  forall vargs1 vargs2 v2,
    (forall k sr b e, i = Some k -> nth (None, Pconst 0) srs k = (Some (b, sr), e) ->
    nth (Vbool true) vargs2 k = Vword (sub_region_addr sr) /\
    wf_sub_region sr (type_of_val v)) ->
    wf_result (emem s2) vargs1 vargs2 i v v2 ->
  write_lval gd r v s1 = ok s1' ->
  exists s2', [/\
    write_lval [::] r2 v2 s2 = ok s2' &
    valid_state rmap2 m0 s1' s2'].
Proof.
  move=> hvs halloc vargs1 vargs2 v2 hvarg2 hrout hw.
  move: halloc; rewrite /alloc_lval_call.
  case: i hvarg2 hrout => [i|] hvarg2; last first.
  + move=> ->.
    t_xrbindP=> _ /check_lval_reg_callP hcheck <- <-.
    case: hcheck.
    + move=> [ii [ty ?]]; subst r.
      move: hw => /= /write_noneP [->] h; exists s2; split => //.
      by rewrite /write_none; case: h => [ [? ->]| [-> ->]].
    move=> [x [? hlx hnnew]]; subst r.
    move: hw; rewrite /= /write_var.
    t_xrbindP=> vm1 hvm1 <- /=.
    by apply: set_varP hvm1=> [v' hv <- | hb hv <-]; rewrite /set_var hv /= ?hb /=;
      eexists;(split;first by reflexivity) => //; apply valid_state_set_var.
  move=> [w [-> hresp]].
  case hnth: nth => [[[b sr]|//] ?].
  t_xrbindP=> x /get_LvarP ? p /get_regptrP hlx {rmap2}rmap2 hset <- <-; subst r.
  have /wf_locals hlocal := hlx.
  move: hw; rewrite /= /write_var.
  t_xrbindP=> vm1 hvm1 <-.
  rewrite /set_var /=.
  case: p hlx hlocal => -[ty pn] pii /= hlx hlocal.
  have /= ? := hlocal.(wfr_rtype); subst ty => /=.
  have := hvarg2 _ _ _ _ refl_equal hnth. move=> [h1 hwf]. (* subst varg2. move=> [[?] hwf]; subst w. *)
  have: w = sub_region_addr sr.
  + have: Vword w = Vword (sub_region_addr sr). rewrite -hresp.(wrp_args). by congruence.
    move=> []. done.
  move=> ?; subst w.

  eexists; split; first by reflexivity.
  set valid_state := valid_state. (* hack due to typeclass interacting badly *)
    apply: set_varP hvm1; last by have /is_sarrP [n {1}->] := hlocal.(wfr_type).
    case: x hlocal hset hlx => -[ty xn] xii /= hlocal hset hlx.
    have /is_sarrP [n] :=  hlocal.(wfr_type). move=> /= ?; subst ty => /=.
    move=> t /to_arrI [n1 [t1 [ht1 hcast]]] <-.
  have:= (valid_state_set_sub_region_regptr hvs _ _ hlx hset (v:=Varr t)). simpl.
  rewrite WArray.castK.
  apply.
  2:move=> _ [<-]; lia.
  rewrite ht1 /= in hwf. apply: wf_sub_region_subtype hwf.
  have /WArray.cast_len /= := hcast. move=> /ZleP. done.
  split. move=> off hmem w hget.
  apply hresp.(wrp_read). rewrite ht1. simpl in hget |- *. have := cast_get8 hcast hget. done.
  done. (*
  
  have /is_sarrP [n {1}->] := hlocal.(wfr_type).
  move=> {v2}.
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
  by eexists; split; first by reflexivity. *)
Qed.

Lemma alloc_call_resP rmap m0 s1 s2 srs ret_pos rs rmap2 rs2 (v:values) s1' :
  valid_state rmap m0 s1 s2 ->
  alloc_call_res pmap rmap srs ret_pos rs = ok (rmap2, rs2) ->
(*   R2 (emem s2) srs i r v -> *)
  forall vargs1 vargs2 v2,
    (forall k sr b e, List.In (Some k) ret_pos -> nth (None, Pconst 0) srs k = (Some (b, sr), e) ->
    nth (Vbool true) vargs2 k = Vword (sub_region_addr sr) /\
    wf_sub_region sr (type_of_val (nth (Vbool true) v k))) ->
    Forall3 (wf_result (emem s2) vargs1 vargs2) ret_pos v v2 ->
  write_lvals gd s1 rs v = ok s1' ->
  exists s2', [/\
    write_lvals [::] s2 rs2 v2 = ok s2' &
    valid_state rmap2 m0 s1' s2'].
Proof.
Admitted.

Lemma Forall2_nth A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall a b i, (i < size la)%nat ->
  R (nth a la i) (nth b lb i).
Proof.
  elim {la lb} => // a b la lb hr _ ih a0 b0 i.
  case: i => [//|i].
  by apply ih.
Qed.

Lemma nth_not_default T x0 (s:seq T) n x :
  nth x0 s n = x ->
  x0 <> x ->
  (n < size s)%nat.
Proof.
  move=> hnth hneq.
  rewrite ltnNge; apply /negP => hle.
  by rewrite nth_default in hnth.
Qed.

Lemma Forall3_nth A B C (R : A -> B -> C -> Prop) la lb lc :
  Forall3 R la lb lc ->
  forall a b c i,
  (i < size la)%nat ->
  R (nth a la i) (nth b lb i) (nth c lc i).
Proof.
  elim {la lb lc} => // a b c la lb lc hr _ ih a0 b0 c0 i.
  case: i => [//|i].
  by apply ih.
Qed.

(* doit-on décrire ce qu'on sait de args avec Rin/Rin_aux ? Ou doit-on faire autrement ?
   Ou peut-on se contenter de valid_state et get_local ?
   En tout cas, il faut dire quelque chose sur les régions de alloc_args retourné par init_params !
*)
Lemma check_resultP rmap m0 s1 s2 srs params (sao_return:option nat) res1 res2 vres1 vargs1 vargs2 :
  valid_state rmap m0 s1 s2 ->
(*  (forall k, sao_return = Some k ->
    exists sr, nth None rs k = Some sr /\
    nth (Vbool true) vargs k = Vword (sub_region_addr sr)) -> *)
  Forall3 (fun osr (x : var_i) v => osr <> None -> size_slot x <= size_val v) srs params vargs1 ->
  List.Forall2 (fun osr varg2 => forall sr, osr = Some sr -> varg2 = Vword (sub_region_addr sr)) srs vargs2 ->
  check_result pmap rmap srs params sao_return res1 = ok res2 ->
  get_var (evm s1) res1 = ok vres1 ->
  exists vres2,
    get_var (evm s2) res2 = ok vres2 /\
    wf_result (emem s2) vargs1 vargs2 sao_return vres1 vres2.
Proof.
  move=> hvs hsize haddr hresult hget.
  move: hresult; rewrite /check_result.
  case: sao_return => [i|].
  + case heq: nth => [sr|//].
    t_xrbindP=> _ /assertP /eqP heqty -[sr' _] /check_validP [bytes [hgvalid -> hmem]].
    move=> /= _ /assertP /eqP ? p /get_regptrP hlres1 <-; subst sr'.
    have /wfr_gptr := hgvalid.
    rewrite /get_var_kind /= /get_local hlres1 => -[_ [[<-] /= ->]].
    eexists; split; first by reflexivity.
    eexists; split; first by reflexivity.
    split.
    + by apply (Forall2_nth haddr None (Vbool true) (nth_not_default heq ltac:(discriminate))).
    + apply (Z.le_trans _ _ _ (size_of_le (type_of_get_var hget))).
      rewrite heqty.
      apply: (Forall3_nth hsize None res1 (Vbool true) (nth_not_default heq ltac:(discriminate))).
      by rewrite heq.
    assert (hval := wfr_val hgvalid hget).
    case: hval => hread hty.
    move=> off w /dup[] /get_val_byte_bound; rewrite hty => hoff.
    apply hread.
    rewrite memi_mem_U8; apply: subset_mem hmem; rewrite subset_interval_of_zone.
    rewrite -(Z.add_0_l off).
    rewrite -(sub_zone_at_ofs_compose _ _ _ (size_slot res1)).
    apply zbetween_zone_byte => //.
    by apply zbetween_zone_refl.
  t_xrbindP=> _ /check_varP hlres1 _ /check_diffP hnnew <-.
  exists vres1; split=> //.
  by have := get_var_kindP hvs hlres1 hnnew hget.
Qed.

Lemma check_resultsP rmap m0 s1 s2 srs params sao_returns res1 res2 vargs1 vargs2 :
  valid_state rmap m0 s1 s2 ->
  Forall3 (fun osr (x : var_i) v => osr <> None -> size_slot x <= size_val v) srs params vargs1 ->
  List.Forall2 (fun osr varg2 => forall sr, osr = Some sr -> varg2 = Vword (sub_region_addr sr)) srs vargs2 ->
  check_results pmap rmap srs params sao_returns res1 = ok res2 ->
  forall vres1,
  mapM (λ x : var_i, get_var (evm s1) x) res1 = ok vres1 ->
  exists vres2,
    mapM (λ x : var_i, get_var (evm s2) x) res2 = ok vres2 /\
    Forall3 (wf_result (emem s2) vargs1 vargs2) sao_returns vres1 vres2.
Proof.
  move=> hvs hsize haddr.
  rewrite /check_results.
  elim: sao_returns res1 res2.
  + move=> [|//] _ [<-] _ [<-] /=.
    eexists; split; first by reflexivity.
    by constructor.
  move=> sao_return sao_returns ih [//|x1 res1] /=.
  t_xrbindP=> _ x2 hresult res2 /ih{ih}ih <-.
  move=> _ v1 hget1 vres1 hgets1 <-.
  have [v2 [hget2 hrout]] := check_resultP hvs hsize haddr hresult hget1.
  have [vres2 [hgets2 hrouts]] := ih _ hgets1.
  rewrite /= hget2 /= hgets2 /=.
  eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma check_results_alloc_params_not_None rmap srs params sao_returns res1 res2 :
  check_results pmap rmap srs params sao_returns res1 = ok res2 ->
  List.Forall (fun oi => forall i, oi = Some i -> nth None srs i <> None) sao_returns.
Proof.
  rewrite /check_results.
  elim: sao_returns res1 res2 => //.
  move=> oi sao_returns ih [//|x1 res1] /=.
  t_xrbindP => _ x2 hresult res2 /ih{ih}ih _.
  constructor=> //.
  move=> i ?; subst oi.
  move: hresult => /=.
  by case: nth.
Qed.

End Section.
