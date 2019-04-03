(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap List StdOrder BitEncoding Bool.
(*---*) import Ring.IntID IntOrder BS2Int.
require import JUtils JArray.

(* -------------------------------------------------------------------- *)
abstract theory BitWord.

op size : {int | 0 < size} as gt0_size.

clone FinType as Alphabet with 
  type t    <- bool,
  op   enum <- [true; false],
  op   card <- 2.

clone include MonoArray with 
  type elem <- bool,
  op dfl <- false,
  op size <- size
  rename "of_list"  as "bits2w"
         "to_list"  as "w2bits"
         "^tP$"     as "wordP"
         "sub"      as "bits"  
  proof ge0_size by (apply ltzW; apply gt0_size).

(* -------------------------------------------------------------------- *)
abbrev modulus = 2 ^ size.

lemma ge2_modulus : 2 <= modulus.
proof.
  rewrite powS_minus ?gt0_size; smt (gt0_size powPos).
qed.

lemma gt0_modulus : 0 < modulus.
proof. smt (ge2_modulus). qed.

lemma ge0_modulus : 0 <= modulus.
proof. smt (ge2_modulus). qed.

lemma max_size : max 0 size = size.
proof. by rewrite /max gt0_size. qed.

hint exact : ge0_size gt0_size gt0_modulus ge2_modulus ge0_modulus max_size.

(* --------------------------------------------------------------------- *)
(* Conversions with int                                                  *)

op of_int (x:int) : t = 
  bits2w (int2bs size (x %% modulus))
axiomatized by of_intE.

op to_uint (w:t) = 
  bs2int (w2bits w)
axiomatized by to_uintE.

op smod (i:int) = 
  if 2^(size - 1) <= i then i - modulus
  else i.

op to_sint (w:t) : int = smod (to_uint w)
axiomatized by to_sintE.

abbrev zero = of_int 0.
abbrev one  = of_int 1.

lemma to_uint_cmp (x : t) : 0 <= to_uint x < modulus.
proof.
  rewrite to_uintE bs2int_ge0 -(size_w2bits x) bs2int_le2Xs.
qed.

lemma of_uintK (x : int) : to_uint (of_int x) = x %% modulus.
proof.
  by rewrite to_uintE of_intE bits2wK 1:size_int2bs // int2bsK // modz_cmp.
qed.

lemma to_uintK : cancel to_uint of_int.
proof.
  move=> w; rewrite to_uintE of_intE.
  rewrite modz_small.
  + by rewrite bs2int_ge0 ger0_norm // -(size_w2bits w) bs2int_le2Xs.
  by rewrite -(size_w2bits w) bs2intK w2bitsK.
qed.

lemma to_uintK' (x: t) : of_int (to_uint x) = x.
proof. by apply to_uintK. qed.

(*hint simplify of_uintK@1. *)
hint simplify to_uintK'@0.

lemma of_sintK (x:int) : 
   to_sint (of_int x) = smod (x %% modulus).
proof. by rewrite to_sintE of_uintK. qed.

lemma to_uint_mod (x : t) : to_uint x %% modulus = to_uint x.
proof. by rewrite modz_small // ger0_norm // to_uint_cmp. qed.

lemma of_int_mod (x : int) : of_int (x %% modulus) = of_int x.
proof. by apply/(can_inj _ _ to_uintK); rewrite !of_uintK modz_mod. qed.

lemma to_uint_small i : 0 <= i < modulus => to_uint (of_int i) = i.
proof. by move=> h; rewrite of_uintK modz_small;solve. qed.

lemma to_uint0 : to_uint (of_int 0) = 0 by [].
lemma to_uint1 : to_uint (of_int 1) = 1 by [].

hint simplify (to_uint0, to_uint1)@0.
hint simplify to_uint_small@1.

lemma word_modeqP (x y : t) :
  to_uint x %% modulus = to_uint y %% modulus => x = y.
proof.
move=> eq_mod; rewrite -(to_uintK x) -(to_uint_mod x).
by rewrite eq_mod to_uint_mod.
qed.

lemma to_uint_eq (x y:t) :  (x = y) <=> (to_uint x = to_uint y).
proof. by rewrite Core.inj_eq // (Core.can_inj _ _  to_uintK). qed.

(* -------------------------------------------------------------------- *)
op int_bit x i = (x%%modulus) %/ 2 ^ i %% 2 <> 0.

lemma of_intwE x i :  
   (of_int x).[i] = (0 <= i < size /\ int_bit x i).
proof.
  rewrite of_intE; case (0 <= i < size) => /= hi; last by rewrite get_out.
  by rewrite get_bits2w // nth_mkseq.
qed.

lemma zerowE i: zero.[i] = false.
proof. by rewrite of_intwE /int_bit. qed.
hint simplify zerowE.
  
lemma of_int_powm1 p i : 
  (of_int (2^p - 1)).[i] = (0 <= i < size /\ i < p).
proof.
  case: (0 <= i < size) => [[h0i his] | hi]; last by rewrite get_out.
  case (0 <= p) => hp; last by rewrite pow_le0 1:/# /= /#.
  have aux : forall p, 0 <= p <= size => (of_int (2 ^ p - 1)).[i] = (true /\ i < p).
  + move=> {p hp} p hp.
    rewrite of_intwE 1:// /int_bit /= (modz_small (2 ^ p - 1)). 
    + smt (gt0_pow2 pow_Mle).
    case (i < p) => hip /=.
    + have -> : p = ((p - i - 1) + 1) + i by ring.
      rewrite h0i his -pow_add // 1:/# divzMDl; 1: smt (gt0_pow2).
      rewrite -pow_add 1:/# //= modzMDl divNz // gt0_pow2.
    by rewrite divz_small //; smt (gt0_pow2 pow_Mle).
  case : (p <= size) => hps; 1: by apply aux.
  rewrite (_:i < p) 1:/# -of_int_mod.
  have -> : p = (p-size) + size by ring.
  rewrite -pow_add 1:/# 1://.
  by rewrite modzMDl -(modzMDl 1 (-1) modulus) /= of_int_mod aux 1:// his.
qed.

lemma get_to_uint w i : w.[i] = (0 <= i < size /\ to_uint w %/ 2 ^ i %% 2 <> 0). 
proof.
  case : (0 <= i < size) => hi;last by rewrite get_out.
  rewrite -{1}(to_uintK w) of_intwE hi /int_bit (modz_small _ modulus) 2://.
  by apply bound_abs; apply to_uint_cmp.  
qed.

lemma b2i_get w i : 0 <= i => b2i w.[i] = to_uint w %/ 2 ^ i %% 2. 
proof. 
  move=> hi;rewrite get_to_uint hi.
  case (i < size) => his //=; 1: smt (modz_cmp).
  rewrite divz_small //; apply bound_abs.
  smt (to_uint_cmp pow_Mle ge0_size).
qed.

lemma bits_divmod w i j: 0 <= i => 0 <= j => bs2int (bits w i j) = ((to_uint w) %/ 2^i) %% 2^j.
proof.
  move => hi; rewrite /bits.
  elim /intind: j.
  + by rewrite mkseq0 bs2int_nil /=.
  move=> j hj hrec; rewrite mkseqS 1:// bs2int_rcons.
  rewrite size_mkseq max_ler 1:// /= hrec.  
  have {2}->:= modz_pow_split (i+j+1) (i+j) (to_uint w) 2 _; 1: smt().
  have hij1 : 2 ^ (i + j + 1) = 2^(j+1) * 2^i.
  + rewrite pow_add 1:/# 1://;congr;ring.
  have hij : 2 ^ (i + j) = 2^j * 2^i.
  + rewrite pow_add 1:/# 1://;congr;ring.
  have h2i0 : 2 ^ i <> 0 by smt (gt0_pow2).
  rewrite -addzA {2}hij1 -mulzA divzMDl 1://. 
  rewrite {2}hij -mulzA divzMDl 1://. 
  rewrite modzMDl !modz_pow2_div; 1,2:smt(). 
  have -> : i + j + 1 - (i + j) = 1 by ring.
  have -> : i + j - i = j by ring.
  rewrite -(pow_add 2 j 1) 1,2:// pow2_1 (modz_small _ (2^j * 2)).
  + by apply bound_abs; smt (modz_cmp gt0_pow2).
  by rewrite addzC mulzC b2i_get 1:/#.  
qed.

lemma bitsE w k len : bits w k len = mkseq (fun (i:int) => w.[k+i]) len.
proof. done. qed.

lemma to_uintRL (w:t) (x:int) : to_uint w = x %% 2^size => w = of_int x.
proof.
  by move=> h;rewrite -of_int_mod; apply: (canRL _ _ _ _ to_uintK).
qed.

lemma to_uint_bits w : to_uint w = bs2int (bits w 0 size).
proof. by rewrite to_uintE /w2bits /bits. qed.

(* -------------------------------------------------------------------- *)
op zerow = zero.

op onew  = of_int (modulus - 1)
axiomatized by oneE.

op (+^) : t -> t -> t = map2 (^^)
axiomatized by xorE.

op andw : t -> t -> t = map2 (/\)
axiomatized by andE.

op oppw (w : t): t = w.

op invw : t -> t = map ([!])
axiomatized by invE.

op orw : t -> t -> t = map2 (\/)
axiomatized by orE.

(* -------------------------------------------------------------------- *)

lemma zerowiE i: zerow.[i] = false.
proof. apply zerowE. qed.

lemma onewE i: onew.[i] = (0 <= i < size).
proof. 
  rewrite oneE; case (0 <= i < size) => hi; 2:by rewrite get_out.  
  by rewrite of_int_powm1 //= 1:/# hi. 
qed.

lemma xorwE w1 w2 i: (w1 +^ w2).[i] = w1.[i] ^^ w2.[i].
proof.
  by rewrite xorE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma andwE (w1 w2:t) i: (andw w1 w2).[i] = (w1.[i] /\ w2.[i]).
proof.
  by rewrite andE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma orwE (w1 w2:t) i: (orw w1 w2).[i] = (w1.[i] \/ w2.[i]).
proof.
  by rewrite orE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma invwE (w:t) i: 
  (invw w).[i] = (0 <= i < size /\ !w.[i]).
proof. by rewrite invE /map initE;case (0 <= i < _). qed.

lemma oppwE (w:t) i: (oppw w).[i] = w.[i].
proof. by []. qed.

hint rewrite bwordE : zerowE zerowiE onewE xorwE andwE invwE.
hint simplify (zerowE, zerowiE, onewE, xorwE, andwE, invwE, orwE).

(* -------------------------------------------------------------------- *)
lemma onew_neq0: onew <> zerow.
proof. 
  apply/negP=> /wordP/(_ 0) /=.
  by rewrite negb_imply neqF.
qed.

lemma xorw0: right_id zero (+^).
proof. by move=> w; apply/wordP=> i _. qed.

lemma xorwA: associative (+^).
proof. by move=> w1 w2 w3; apply/wordP=> i _; rewrite !bwordE xorA. qed.

lemma xorwC: commutative (+^).
proof. by move=> w1 w2; apply/wordP=> i _; rewrite !bwordE xorC. qed.

lemma xorwK: forall x, x +^ x = zero.
proof. by move=> w; apply/wordP=> i _; rewrite !bwordE. qed.

lemma andw1: right_id onew andw.
proof. by move=> w; apply/wordP=> i h; rewrite !bwordE h. qed.

lemma andwA: associative andw.
proof. by move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE andbA. qed.

lemma andwC: commutative andw.
proof. by move=> w1 w2; apply/wordP=> i h; rewrite !bwordE andbC. qed.

lemma andwDl: left_distributive andw (+^).
proof. move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE smt. qed.

lemma andwK: idempotent andw.
proof. by move=> x; apply/wordP=> i h; rewrite !bwordE andbb. qed.

(* -------------------------------------------------------------------- *)
instance bring with t
  op rzero = zerow
  op rone  = onew
  op add   = (+^)
  op mul   = andw
  op opp   = oppw

  proof oner_neq0 by apply/onew_neq0
  proof addr0     by apply/xorw0
  proof addrA     by (move=> w1 w2 w3; rewrite xorwA)
  proof addrC     by apply/xorwC
  proof addrK     by apply/xorwK
  proof mulr1     by apply andw1
  proof mulrA     by (move=> w1 w2 w3; rewrite andwA)
  proof mulrC     by apply/andwC
  proof mulrDl    by apply/andwDl
  proof mulrK     by apply/andwK
  proof oppr_id   by trivial.

pred unitw (w:t) = w = onew.
op iandw (w:t) = if w = onew then onew else w.

clone Ring.ComRing as WRing with 
   type t <- t,
   op zeror <- zero,
   op ( + ) <- (+^),
   op [ - ] <- oppw,
   op oner  <- onew,
   op ( * ) <- andw, 
   op invr  <- iandw,
   pred unit <- unitw
proof *.
realize addrA.     proof. apply xorwA. qed.
realize addrC.     proof. apply xorwC. qed.
realize add0r.     proof. move=> ?;ring. qed.
realize addNr.     proof. move=> ?;ring. qed.
realize oner_neq0. proof. apply onew_neq0. qed.
realize mulrA.     proof. apply andwA. qed.
realize mulrC.     proof. apply andwC. qed.
realize mul1r.     proof. move=> ?;ring. qed. 
realize mulrDl.    proof. apply andwDl. qed. 
realize mulVr.     proof. move=> ?;rewrite /unitw /iandw => -> /=;ring. qed.
realize unitout.   proof. by move=> x;rewrite /unitw /iandw => ->. qed.

realize unitP. 
proof. 
move=> x y; rewrite /unitw !wordP => + i Hi -/(_ i Hi).
by rewrite andwE onewE Hi /#.
qed.

lemma xor0w w : of_int 0 +^ w = w.
proof. by apply WRing.add0r. qed.

lemma xorw0_s w : w +^ of_int 0 = w.
proof. by apply WRing.addr0. qed.

lemma xorw1 w : w +^ onew = invw w.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma xor1w w : onew +^ w = invw w.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma and0w w : andw (of_int 0) w = of_int 0.
proof. by apply WRing.mul0r. qed.

lemma andw0 w : andw w (of_int 0) = of_int 0.
proof. by apply WRing.mulr0. qed.

lemma and1w w : andw onew w = w.
proof. by apply WRing.mul1r. qed.

lemma andw1_s w : andw w onew = w.
proof. by apply WRing.mulr1. qed.

lemma orw0 w : orw w zero = w.
proof. by apply wordP => i hi. qed.  

lemma or0w w : orw zero w = w.
proof. by apply wordP => i hi. qed.  

lemma orw1 w : orw w onew = onew.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma or1w w : orw onew w = onew.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma orwK w : orw w w = w.
proof. by apply wordP => i hi /=; case (w.[i]). qed.

lemma xorwK_s w1 w2 : w1 = w2 => (w1 +^ w2) = zero.
proof. move=> ->;apply xorwK. qed.

lemma andwK_s w1 w2 : w1 = w2 => andw w1 w2 = w1.
proof. move=> ->;apply andwK. qed.

lemma orwK_s w1 w2 : w1 = w2 => orw w1 w2 = w1.
proof. move=> ->;apply orwK. qed.

hint simplify (xor0w, xorw0_s, xorw1, xor1w,
               and0w, andw0, and1w, andw1_s,
               or0w, orw0, orw1, or1w, 
               xorwK_s, andwK_s, orwK_s).

(* --------------------------------------------------------------------- *)
(* Arimethic operations                                                  *)

op ulift1 (f : int -> int) (w : t) =
  of_int (f (to_uint w)).

op ulift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_uint w1) (to_uint w2)).

op slift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_uint w1) (to_uint w2)).

op ( + ) = ulift2 Int.( + ) axiomatized by addE.
op ([-]) = ulift1 Int.([-]) axiomatized by oppE.
op ( * ) = ulift2 Int.( * ) axiomatized by mulE.

op (\udiv) = ulift2 IntDiv.( %/) axiomatized by udivE.
op (\umod) = ulift2 IntDiv.( %/) axiomatized by umodE.

(* TODO check this *)
op (\sdiv) = slift2 IntDiv.( %/) axiomatized by sdivE.
op (\smod) = slift2 IntDiv.( %/) axiomatized by smodE.

(* --------------------------------------------------------------------- *)
(* Comparisons                                                           *)

op (\ule) (x y : t) = (to_uint x) <= (to_uint y) axiomatized by uleE.
op (\ult) (x y : t) = (to_uint x) <  (to_uint y) axiomatized by ultE.

op (\sle) (x y : t) = (to_sint x) <= (to_sint y) axiomatized by sleE.
op (\slt) (x y : t) = (to_sint x) <  (to_sint y) axiomatized by sltE.

lemma ult_of_int x y :
   (of_int x \ult of_int y) = (x %% modulus < y %% modulus).
proof. by rewrite ultE /= !of_uintK. qed.

lemma ule_of_int x y :
   (of_int x \ule of_int y) = (x %% modulus <= y %% modulus).
proof. by rewrite uleE /= !of_uintK. qed.

lemma uleNgt x y : x \ule y <=> ! y \ult x.
proof. by rewrite ultE uleE lerNgt. qed.

lemma ultNge x y: x \ult y <=> ! y \ule x.
proof. by rewrite ultE uleE ltzNge. qed.

lemma ult_of_int_true x y :
   (x %% modulus < y %% modulus) => (of_int x \ult of_int y) = true.
proof. by rewrite ult_of_int => ->. qed.

lemma ult_of_int_false x y :
   !(x %% modulus < y %% modulus) => (of_int x \ult of_int y) = false.
proof. by rewrite ult_of_int => ->. qed.

lemma ule_of_int_true x y :
   (x %% modulus <= y %% modulus) => (of_int x \ule of_int y) = true.
proof. by rewrite ule_of_int => ->. qed.

lemma ule_of_int_false x y :
   !(x %% modulus <= y %% modulus) => (of_int x \ule of_int y) = false.
proof. by rewrite ule_of_int => ->. qed.

hint simplify (ult_of_int_true, ult_of_int_false, ule_of_int_true, ule_of_int_false).

(* --------------------------------------------------------------------- *)
(* ComRing                                                               *)

op is_inverse (w wi: t) = wi * w = of_int 1.
op unit (w:t) = exists wi, is_inverse w wi.
op invr (w:t) = Logic.choiceb (is_inverse w) w.

lemma of_intN (x : int) : of_int (-x) = - of_int x.
proof.
rewrite oppE /ulift1 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod modzNm.
qed.

lemma to_uintN (x : t) : to_uint (-x) = (- to_uint x) %% modulus.
proof. by rewrite oppE /ulift1 of_uintK. qed.

lemma of_intD (x y : int) : of_int (x + y) = of_int x + of_int y.
proof.
rewrite addE /ulift2 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod !(modzDml, modzDmr).
qed.

lemma to_uintD (x y : t) : to_uint (x + y) = (to_uint x + to_uint y) %% modulus.
proof. by rewrite addE /ulift2 of_uintK. qed.

lemma of_intM (x y : int) : of_int x * of_int y = of_int (x * y).
proof.
rewrite mulE /ulift2 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod !(modzMml, modzMmr).
qed.

lemma to_uintM (x y : t) : to_uint (x * y) = (to_uint x * to_uint y) %% modulus.
proof. by rewrite mulE /ulift2 !of_uintK. qed.

lemma to_uintD_small (x y : t) : to_uint x + to_uint y < modulus => 
  to_uint (x + y) = to_uint x + to_uint y.
proof. 
  move=> h;rewrite to_uintD modz_small 2://; smt (to_uint_cmp). 
qed.

lemma to_uintM_small (x y : t) : to_uint x * to_uint y < modulus => 
  to_uint (x * y) = (to_uint x * to_uint y).
proof. 
  move=> h;rewrite to_uintM modz_small 2://; smt (to_uint_cmp). 
qed.

clone export Ring.ComRing as WRingA with 
   type t <- t,
   op zeror <- of_int 0,
   op ( + ) <- BitWord.( + ),
   op [ - ] <- BitWord.([-]),
   op oner  <- of_int 1,
   op ( * ) <- BitWord.( * ),
   op invr  <- invr,
   pred unit  <- BitWord.unit proof *.

realize addrA.
proof. 
  move=> x y z; rewrite addE /ulift2 !to_uintD -of_int_mod modzDmr.
  by rewrite -(of_int_mod (_ + to_uint z)) modzDml addrA.
qed.

realize addrC.
proof. by move=> x y; rewrite !addE /ulift2 addzC. qed.

realize add0r.
proof. by move=> x; rewrite addE /ulift2; cbv delta. qed.

realize addNr.
proof. 
  move=> x; rewrite addE oppE /ulift2 /ulift1 of_uintK.
  by rewrite -of_int_mod modzDml addNz.
qed.

realize oner_neq0.
proof. 
  apply /negP => heq.
  have := of_uintK 1; rewrite heq of_uintK mod0z.
  rewrite modz_small //;smt (ge2_modulus).
qed.

realize mulrA.
 move=> x y z; rewrite mulE /ulift2 !to_uintM -of_int_mod modzMmr.
  by rewrite -(of_int_mod (_ * to_uint z)) modzMml mulrA.
qed.

realize mulrC.
proof. by move=> x y; rewrite !mulE /ulift2 mulzC. qed.

realize mul1r.
proof. by move=> x; rewrite mulE /ulift2 to_uint1. qed.

realize mulrDl.
proof. 
  move=> x y z; rewrite !addE !mulE /ulift2.
  rewrite !of_uintK -of_int_mod modzMml eq_sym.  
  by rewrite -of_int_mod modzDml modzDmr mulrDl.
qed.

realize mulVr.
proof. by move=> x /choicebP /= ->. qed.

realize unitP.
proof. by move=> w wi hinv;exists wi. qed.

realize unitout.
proof. by move=> x /negb_exists /=; apply choiceb_dfl. qed.

abbrev (^) = WRingA.exp.

lemma ofintS (n : int) : 0 <= n => of_int (n + 1) = of_int 1 + of_int n.
proof. by rewrite of_intD addrC. qed. 

lemma to_uintB (x y: t) : y \ule x => to_uint (x - y) = to_uint x - to_uint y.
proof.
  rewrite uleE=> hle.
  rewrite to_uintD to_uintN modzDmr modz_small //; smt (to_uint_cmp).
qed.

(* Add simplification rule for rewriting *)
(* FIXME add direction for hint simplify *)
lemma of_intN' (x : int) : - of_int x = of_int (-x).
proof. by rewrite of_intN. qed.

lemma of_intS (x y : int) : of_int (x - y) = of_int x - of_int y.
proof. by rewrite of_intD of_intN. qed.

lemma of_intS' (x y : int) : of_int x - of_int y = of_int (x - y).
proof. by rewrite of_intS. qed.

lemma of_intD' (x y : int) : of_int x + of_int y = of_int (x + y).
proof. by rewrite of_intD. qed.

lemma of_intM' (x y : int) : of_int x * of_int y = of_int (x * y).
proof. by rewrite of_intM. qed.

hint simplify (of_intS', of_intM')@0.
hint simplify (of_intD')@1.

lemma addr0_s w : w + of_int 0 = w.
proof. by apply addr0. qed.

lemma add0r_s w : of_int 0 + w = w.
proof. by apply add0r. qed.

lemma mulr1_s w : w * of_int 1 = w.
proof. by apply mulr1. qed.

lemma mul1r_s w : of_int 1 * w = w.
proof. by apply mul1r. qed.

lemma mulr0_s w : w * of_int 0 = of_int 0.
proof. by apply mulr0. qed.

lemma mul0r_s w : of_int 0 * w = of_int 0.
proof. by apply mul0r. qed.

lemma addA_ofint w i j : w + of_int i + of_int j = w + of_int (i + j).
proof. by rewrite -addrA. qed.

lemma addS_ofint w i j : w + of_int i - of_int j = w + of_int (i - j).
proof. by rewrite -addrA -of_intS. qed.

hint simplify (addr0_s, add0r_s, mul1r_s, mulr1_s, mul0r_s, mulr0_s, addA_ofint).



(* --------------------------------------------------------------------- *)
(* Ring tactic                                                           *)

op zerow_ring = of_int 0.
op onew_ring  = of_int 1.

instance ring with t
  op rzero = BitWord.zerow_ring
  op rone  = BitWord.onew_ring
  op add   = BitWord.( + )
  op opp   = BitWord.([-])
  op mul   = BitWord.( * )
  op expr  = WRingA.exp
  op ofint = BitWord.of_int 

  proof oner_neq0 by apply oner_neq0
  proof addr0     by apply addr0
  proof addrA     by apply addrA
  proof addrC     by apply addrC
  proof addrN     by apply addrN
  proof mulr1     by apply mulr1
  proof mulrA     by apply mulrA
  proof mulrC     by apply mulrC
  proof mulrDl    by apply mulrDl
  proof expr0     by apply expr0
  proof exprS     by apply exprS
  proof ofint0    by done
  proof ofint1    by done
  proof ofintS    by apply ofintS
  proof ofintN    by apply of_intN.

(* --------------------------------------------------------------------- *)
(* Exact arithmetic operations                                           *)
op subc : t -> t -> bool -> bool * t.
op addc : t -> t -> bool -> bool * t.
op mulu : t -> t -> t * t.

(* --------------------------------------------------------------------- *)
(* Bitwize operations                                                    *)

abbrev (`&`) = andw.
abbrev (`|`) = orw.
abbrev (`^`) = (+^).

op (`>>>`) (x : t) (i : int) =
  init (fun j => x.[j + i])
axiomatized by wlsrE.

op (`<<<`) (x : t) (i : int) =
  init (fun j => x.[j - i])
axiomatized by wlslE.

lemma shlwE w k i : (w `<<<` k).[i] = (0 <= i < size && w.[i - k]).
proof. by rewrite wlslE initE. qed.

lemma shrwE w k i : (w `>>>` k).[i] = (0 <= i < size && w.[i + k]).
proof. by rewrite wlsrE initE. qed.
hint simplify (shrwE, shlwE).

lemma int_bitMP i j k : 0 <= k => 0 <= j < size =>
  int_bit (i * 2 ^ k) j = (0 <= j - k < size /\ int_bit i (j - k)).
proof.
  move=> hk [h0j hjs];rewrite /int_bit modz_pow2_div 1:/# modz_dvd.
  + by apply (dvdz_exp2l 2 1) => /#.
  case: (0 <= j - k < size) => [ [hjk1 hjk2] | hjk]  /=;last first.
  + have hlt : (j < k) by smt().   
    have ->: k = (k-j-1) + 1 + j by ring.
    rewrite -pow_add 1:/# 1:// -mulzA mulzK; 1: smt (gt0_pow2).
    by rewrite -pow_add 1:/# //= -mulzA modzMl.
  rewrite (modz_pow2_div size) 1:/# modz_dvd.
  + by apply (dvdz_exp2l 2 1) => /#.
  have {1}-> : j = (j - k) + k by ring.
  by rewrite -pow_add 1,2:// divzMpr 1:gt0_pow2. 
qed.

lemma int_bitDP i j k : 0 <= i < modulus => 0 <= k => 0 <= j < size =>
  int_bit (i %/ 2 ^ k) j = (0 <= j + k < size /\ int_bit i (j + k)).
proof.
  move=> hi hk [h0j hjs];rewrite /int_bit.
  rewrite !(modz_small _ modulus); 1,2: apply bound_abs; 2:done.
  + by apply divz_cmp; [apply gt0_pow2 | smt (gt0_pow2)].
  case: (0 <= j + k < size) => hjk.
  + have {1}->:= divz_eq i (2^(j+k)).
    have {1}->:= divz_eq (i %% 2 ^ (j + k)) (2^k).
    pose id := i %/ 2 ^ (j + k). pose im := i %% 2 ^ (j + k).
    have -> : id * 2 ^ (j + k) + (im %/ 2 ^ k * 2 ^ k + im %% 2 ^ k) =
           (id * 2^j + im %/ 2 ^ k) * 2^k + im %% 2 ^ k.
    + by rewrite -pow_add 1,2://;ring.
    rewrite divzMDl. smt (gt0_pow2).
    rewrite (divz_small (im %% 2 ^ k) (2 ^ k)).
    + apply bound_abs;apply modz_cmp;apply gt0_pow2.
    rewrite /= divzMDl. smt (gt0_pow2).
    rewrite (divz_small (im %/ 2 ^ k) (2 ^ j)) 2://.
    apply bound_abs; apply divz_cmp; 1:by apply gt0_pow2. 
    by rewrite pow_add 1,2://;apply modz_cmp;apply gt0_pow2.
  rewrite /= (divz_small (i %/ 2 ^ k) (2 ^ j)) 2://.
  apply bound_abs;apply divz_cmp; 1: by apply gt0_pow2.  
  rewrite pow_add 1,2://;smt (pow_Mle).
qed.

lemma shlMP i k : 0 <= k => (of_int i `<<<` k) = of_int (i * 2^k).
proof.
  by move=> hk;apply wordP => j hj; rewrite shlwE !of_intwE hj /= -int_bitMP.
qed.

lemma shrDP i k : 0 <= k => (of_int i `>>>` k) = of_int (i %% modulus %/ 2^k).
proof.
  move=> hk;rewrite -(of_int_mod i).
  apply wordP => j hj; rewrite shrwE !of_intwE hj /= -int_bitDP //.
  by apply modz_cmp.
qed.

lemma to_uint_shl (w:t) i : 
  0 <= i => to_uint (w `<<<` i) = (to_uint w * 2^ i) %% modulus.
proof.
  by move=> hi; rewrite -{1}(to_uintK w) shlMP 1:// of_uintK.
qed.

lemma to_uint_shr (w:t) i : 
  0 <= i => to_uint (w `>>>` i) = to_uint w %/ 2^ i.
proof.
  move=> hi;rewrite -{1}(to_uintK w) shrDP 1:// of_uintK.
  rewrite (modz_small (to_uint w)).  
  + by apply bound_abs; apply to_uint_cmp.
  rewrite modz_small 2://.
  apply bound_abs; apply divz_cmp; [apply gt0_pow2 | ].
  smt (to_uint_cmp gt0_pow2).
qed.
    
lemma shrw_shlw w i : w `>>>` i = w `<<<` (-i).
proof. by apply wordP => k hk /=. qed.

lemma shrw_add w i j : 0 <= i => 0 <= j => w `>>>` i `>>>` j = w `>>>` (i + j).
proof.
  move=> hi hj; apply wordP => k hk /=;rewrite hk /=.
  case : (0 <= k + j < size) => hkj /=; 1:congr;ring.
  by rewrite get_out 1:/#.
qed.

lemma shrw_out w i : size <= i => w `>>>` i = zero.
proof.
  by move=> hi;apply wordP => k hk/=; rewrite get_out 1:/#.
qed.
hint simplify (shrw_add, shrw_out).

lemma shlw_add w i j : 0 <= i => 0 <= j => w `<<<` i `<<<` j = w `<<<` (i + j).
proof.
  move=> hi hj; apply wordP => k hk /=;rewrite hk /=.
  case : (0 <= k - j < size) => hkj /=; 1:congr;ring.
  by rewrite get_out 1:/#.
qed.

lemma shlw_out w i : size <= i => w `<<<` i = zero.
proof.
  by move=> hi;apply wordP => k hk/=; rewrite get_out 1:/#.
qed.
hint simplify (shlw_add, shlw_out).

lemma shrw_map2 f w1 w2 i : f false false = false => 
   (map2 f) (w1 `>>>` i) (w2 `>>>` i) = (map2 f w1 w2) `>>>` i.
proof.
  move=> hf;apply wordP => k hk. 
  rewrite map2iE // !shrwE hk.
  case: (0 <= k + i < size) => hki; 1: by rewrite map2iE.
  by rewrite !get_out.
qed.

lemma shlw_map2 f w1 w2 i : f false false = false => 
   (map2 f) (w1 `<<<` i) (w2 `<<<` i) = (map2 f w1 w2) `<<<` i.
proof.
  move=> hf;apply wordP => k hk. 
  rewrite map2iE // !shlwE hk.
  case: (0 <= k - i < size) => hki; 1: by rewrite map2iE.
  by rewrite !get_out.
qed.

lemma shrw_and w1 w2 i : (w1 `>>>` i) `&` (w2 `>>>` i) = (w1 `&` w2) `>>>` i.
proof. by rewrite andE shrw_map2. qed.

lemma shrw_xor w1 w2 i : (w1 `>>>` i) `^` (w2 `>>>` i) = (w1 `^` w2) `>>>` i.
proof. by rewrite xorE shrw_map2. qed.

lemma shrw_or w1 w2 i : (w1 `>>>` i) `|` (w2 `>>>` i) = (w1 `|` w2) `>>>` i.
proof. by rewrite orE shrw_map2. qed.

lemma shlw_and w1 w2 i : (w1 `<<<` i) `&` (w2 `<<<` i) = (w1 `&` w2) `<<<` i.
proof. by rewrite andE shlw_map2. qed.

lemma shlw_xor w1 w2 i : (w1 `<<<` i) `^` (w2 `<<<` i) = (w1 `^` w2) `<<<` i.
proof. by rewrite xorE shlw_map2. qed.

lemma shlw_or w1 w2 i : (w1 `<<<` i) `|` (w2 `<<<` i) = (w1 `|` w2) `<<<` i.
proof. by rewrite orE shlw_map2. qed.

hint simplify (shrw_and, shrw_xor, shrw_or, shlw_and, shlw_xor, shlw_or).

op ror (x : t) (i : int) = 
  init (fun j => x.[(j + i) %% size])
axiomatized by rorE.

op rol (x : t) (i : int) = 
  init (fun j => x.[(j - i) %% size])
axiomatized by rolE.

lemma rorwE w k i : 
  (ror w k).[i] = if (0 <= i < size) then w.[(i+k) %% size] else false.
proof. by rewrite rorE initE. qed.

lemma rolwE w k i : 
  (rol w k).[i] = if (0 <= i < size) then w.[(i-k) %% size] else false.
proof. by rewrite rolE initE. qed.

hint simplify (rorwE, rolwE).

lemma rol_xor w i : 0 <= i < size => 
  rol w i = (w `<<<` i) `^` (w `>>>` (size - i)).
proof.
  move=> hi; apply wordP => k hk /=.
  rewrite hk /=. 
  case (0 <= k - i < size) => hki.
  + rewrite modz_small; 1: by apply bound_abs.
    by rewrite (get_out _ (k + (size - i))) 1:/#.
  rewrite modz_sub_carry // 1:/# (get_out _ _ hki) /=.
  by congr;ring.
qed.

lemma rol_xor_simplify w1 w2 i si: 
   w1 = w2 => si = size - i => 0 <= i < size => 
   (w1 `<<<` i) `^` (w2 `>>>` si) = rol w1 i.
proof. by move=> 2!-> hi;rewrite rol_xor. qed.

(* --------------------------------------------------------------------- *)
(* Like between bitwize operations and arithmetic operations             *)

lemma and_mod k w : 
  0 <= k => 
    w `&` of_int (2^k - 1) = of_int (to_uint w %% 2^k).
proof.
  move=> hk;apply wordP => i hi /=.
  rewrite of_int_powm1 of_intwE hi /= /int_bit.  
  rewrite (modz_small _ modulus).
  + apply bound_abs; smt (le_modz modz_cmp to_uint_cmp gt0_pow2).
  case (i < k) => hik /=.
  + rewrite modz_pow2_div 1:/# modz_dvd.
    + by apply (dvdz_exp2l 2 1) => /#.
    by rewrite get_to_uint hi.
  rewrite divz_small 2://; smt (gt0_pow2 modz_cmp pow_Mle).
qed.

lemma to_uint_and_mod k w : 
  0 <= k => 
    to_uint (w `&` of_int (2^k - 1)) = to_uint w %% 2^k.
proof.
  move=> hk ; rewrite and_mod 1:// of_uintK modz_small //. 
  apply bound_abs; smt (le_modz to_uint_cmp gt0_pow2 modz_cmp).
qed.

end BitWord.

theory W8.
  abbrev [-printing] size = 8.
  clone include BitWord with op size <- 8
  proof gt0_size by done.

  op (`>>`) (w1 w2 : W8.t) = w1 `>>>` (to_uint w2 %% size).
  op (`<<`) (w1 w2 : W8.t) = w1 `<<<` (to_uint w2 %% size). 

  lemma shr_div w1 w2 : to_uint (w1 `>>` w2) = to_uint w1 %/ 2^ (to_uint w2 %% size).
  proof.
    rewrite -{1}(to_uintK w1) /(`>>`) shrDP; 1: smt (modz_cmp).
    rewrite of_uintK to_uint_mod modz_small 2://.
    apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
    by have:= to_uint_cmp w1; smt (gt0_pow2).
  qed.

  lemma shr_div_le w1 i : 0 <= i < size => 
       to_uint (w1 `>>` (of_int i)) = to_uint w1 %/ 2^i.
  proof.
    move=> hi;rewrite shr_div of_uintK.
    rewrite (modz_small i);1: smt (pow2_8).
    by rewrite modz_small.
  qed.

  lemma rol_xor_shft w i : 0 < i < size => 
    rol w i = (w `<<` of_int i) +^ (w `>>` of_int (size - i)).
  proof.
    move=> hi; rewrite /(`<<`) /(`>>`) !of_uintK /=.
    by rewrite !(modz_small _ 256) 1,2:/# !modz_small 1,2:/# rol_xor 1:/#.
  qed.
end W8. export W8. 

abstract theory WT.
  type t.
  op size : int.
  axiom gt0_size : 0 < size.

  op "_.[_]" : t -> int -> bool.
  op init : (int -> bool) -> t.

  op andw : t -> t -> t.
  op orw  : t -> t -> t.
  op (+^) : t -> t -> t.
  
  op (+) : t -> t -> t.

  op (`>>`) : t -> W8.t -> t. 
  op (`<<`) : t -> W8.t -> t.
  op rol : t -> int -> t.
  op of_int : int -> t.
  op to_uint : t -> int.
  op to_sint : t -> int.

  op bits : t -> int -> int -> bool list.

  axiom initiE (f : int -> bool) (i : int) : 0 <= i < size => (init f).[i] = f i.
  
  axiom andwE (w1 w2 : t) (i : int) : (andw w1 w2).[i] = (w1.[i] /\ w2.[i]).
  axiom orwE  (w1 w2 : t) (i : int) : (orw  w1 w2).[i] = (w1.[i] \/ w2.[i]).
  axiom xorwE (w1 w2 : t) (i : int) : (w1 +^ w2).[i] = (w1.[i] ^^ w2.[i]).

  axiom wordP (w1 w2 : t) :
    w1 = w2 <=> forall (i : int), 0 <= i < size => w1.[i] = w2.[i].

  axiom to_uint_cmp (x : t) : 0 <= to_uint x < 2^size.

  op int_bit x i = (x%%2^size) %/ 2 ^ i %% 2 <> 0.

  axiom of_intwE x i :  
   (of_int x).[i] = (0 <= i < size /\ int_bit x i).

  axiom get_to_uint w i : w.[i] = (0 <= i < size /\ to_uint w %/ 2 ^ i %% 2 <> 0). 

  axiom bitsE w k len : bits w k len = mkseq (fun (i:int) => w.[k+i]) len.

  axiom bits_divmod w i j: 0 <= i => 0 <= j => 
    bs2int (bits w i j) = ((to_uint w) %/ 2^i) %% 2^j.

  axiom to_uintRL (w:t) (x:int) : to_uint w = x %% 2^size => w = of_int x.

  axiom to_uint_bits w : to_uint w = bs2int (bits w 0 size).

  axiom of_uintK (x : int) : to_uint (of_int x) = x %% 2^size.

  axiom to_uintK : cancel to_uint of_int.

  axiom of_int_mod (x : int) : of_int (x %% 2^size) = of_int x.

  axiom and_mod k w : 
    0 <= k => 
      andw w (of_int (2^k - 1)) = of_int (to_uint w %% 2^k).

  axiom rol_xor_shft w i : 0 < i < size => 
    rol w i = (w `<<` W8.of_int i) +^ (w `>>` W8.of_int (size - i)).

end WT.

abstract theory W_WS.

  op sizeS : int.
  op sizeB : int. 
  op r : int.
  axiom gt0_r : 0 < r.
  axiom sizeBrS : sizeB = r * sizeS.

  clone import WT as WS with op size <- sizeS.
  clone import WT as WB with op size <- sizeB.

  clone export MonoArray as Pack with 
    type elem <- WS.t,
    op dfl <- WS.of_int 0,
    op size <- r
    proof ge0_size by smt (gt0_r)
    rename [type] "t" as "pack_t"
           [lemma] "tP" as "packP".

  lemma le_size : sizeS <= sizeB.
  proof. rewrite sizeBrS;smt (gt0_r WS.gt0_size WB.gt0_size). qed.

  lemma in_bound i j : 0 <= i < r => 0 <= j < sizeS => 0 <= i * sizeS + j < sizeB.
  proof.
    move=> hi hj;rewrite sizeBrS;have : i * sizeS + j < (i+1) * sizeS; smt ().
  qed.

  (* ------------------------------------------------ *)

  op sigextu'B   (w:WS.t) = WB.of_int (WS.to_sint w).
  op zeroextu'B  (w:WS.t) = WB.of_int (WS.to_uint w).
  op truncateu'S (w:WB.t) = WS.of_int (WB.to_uint w).

  hint exact : WS.gt0_size WB.gt0_size. 

  lemma size_div : sizeS %| sizeB.
  proof. by rewrite dvdzP sizeBrS;exists r. qed.

  lemma div_size : sizeB %/ sizeS = r.
  proof. rewrite sizeBrS mulzK; smt (WS.gt0_size). qed.

  op (\bits'S) (w:WB.t) i = WS.init (fun j => w.[ i * sizeS + j])
  axiomatized by bits'SE.

  op unpack'S (w:WB.t) : pack_t = 
    Pack.init (fun i => w \bits'S i).

  abbrev to_list (w:WB.t) : WS.t list = Pack.to_list (unpack'S w).

  op pack'R_t (ws:pack_t) = 
    WB.init (fun i => ws.[i %/ sizeS].[i %% sizeS])
  axiomatized by pack'RE.

  abbrev pack'R (ws:WS.t list) = pack'R_t (Pack.of_list ws).
 
  lemma pack'RwE (ws:pack_t) i : 0 <= i < sizeB => 
    (pack'R_t ws).[i] = ws.[i %/ sizeS].[i %% sizeS].
  proof. by move=> hi;rewrite pack'RE initiE //. qed.

  lemma get_unpack'S w i : 0 <= i < r => 
    (unpack'S w).[i] = w \bits'S i.
  proof. apply initiE. qed.

  lemma bits'SiE w i j : 0 <= j < sizeS => 
    (w \bits'S i).[j] = w.[i * sizeS + j].
  proof. by move=> hj; rewrite bits'SE initiE. qed.
  
  lemma get_bits'S (w:WB.t) i : 
    0 <= i < sizeB => 
    w.[i] = (w \bits'S (i%/ sizeS)).[i %% sizeS].
  proof. 
    by move=> hi; rewrite bits'SE WS.initiE /= -?divz_eq; 1:by apply modz_cmp.
  qed.

  lemma get_out (w:WB.t) i : 
     !(0 <= i < r) => 
     w \bits'S i = WS.of_int 0.
  proof.
    move=> hi;apply WS.wordP => k hk.
    rewrite bits'SiE 1:// WS.of_intwE /WS.int_bit /= get_to_uint. 
    smt(gt0_r WS.gt0_size sizeBrS).
  qed.

  lemma get_zero i : WB.of_int 0 \bits'S i = WS.of_int 0.
  proof.
    apply WS.wordP => k hk.
    by rewrite bits'SiE 1:// WS.of_intwE /WS.int_bit /= get_to_uint /= WB.of_uintK.
  qed.

  lemma unpack'SK w : pack'R_t (unpack'S w) = w.
  proof.
    apply wordP => i hi; rewrite pack'RE initiE //= get_bits'S //.
    by rewrite get_unpack'S //;apply divz_cmp => //;rewrite -sizeBrS.
  qed.
     
  lemma pack'RbE ws i : 0 <= i < r => pack'R_t ws \bits'S i = ws.[i].
  proof. 
    move=> hr;apply WS.wordP => j hj.
    rewrite bits'SiE // pack'RE initiE /= ?in_bound //.
    by rewrite modzMDl divzMDl 1:/# divz_small ?modz_small; solve.
  qed.

  lemma pack'RK ws : unpack'S (pack'R_t ws) = ws.
  proof. by apply packP => i hi; rewrite get_unpack'S // pack'RbE. qed.

  lemma wordP (w1 w2 :WB.t) : (forall i, 0 <= i < r => w1 \bits'S i = w2 \bits'S i) => w1 = w2.
  proof.
    move=> h; rewrite -(unpack'SK w1) -(unpack'SK w2); congr.
    by apply Pack.packP => i hi; rewrite !get_unpack'S 1,2://; apply h.
  qed.

  lemma allP (w1 w2 :WB.t) : all (fun i => w1 \bits'S i = w2 \bits'S i) (iota_ 0 r) => w1 = w2.
  proof. rewrite allP => h; apply wordP => i; rewrite -(mema_iota 0 r); apply h. qed.

  abbrev map (f:WS.t -> WS.t) (w:WB.t) = 
    pack'R_t (map f (unpack'S w)).

  abbrev map2 (f:WS.t -> WS.t -> WS.t) (w1 w2:WB.t) = 
    pack'R_t (map2 f (unpack'S w1) (unpack'S w2)).

  lemma mapbE f w i : 0 <= i < r => 
    (map f w) \bits'S i = f (w \bits'S i).
  proof.
    by move=> hi;rewrite pack'RbE // mapiE // initiE.
  qed.

  lemma map2bE f w1 w2 i : 0 <= i < r => 
    (map2 f w1 w2) \bits'S i = f (w1 \bits'S i) (w2 \bits'S i).
  proof.
    by move=> hi;rewrite pack'RbE // map2iE // !initiE.
  qed.

  lemma andb'SE (w1 w2:WB.t) i : 
    (WB.andw w1 w2) \bits'S i = WS.andw (w1 \bits'S i) (w2 \bits'S i).
  proof.
    apply WS.wordP => j hj.
    by rewrite bits'SiE // WB.andwE WS.andwE !bits'SiE.
  qed.

  lemma orb'SE (w1 w2:WB.t) i : 
    (WB.orw w1 w2) \bits'S i = WS.orw (w1 \bits'S i) (w2 \bits'S i).
  proof.
    apply WS.wordP => j hj.
    by rewrite bits'SiE // WB.orwE WS.orwE !bits'SiE.
  qed.

  lemma xorb'SE (w1 w2:WB.t) i :
    (WB.(+^) w1 w2) \bits'S i = WS.(+^) (w1 \bits'S i) (w2 \bits'S i).
  proof.
   apply WS.wordP => j hj.
    by rewrite bits'SiE // WB.xorwE WS.xorwE !bits'SiE.
  qed.

  lemma andb'Ru'SE ws1 ws2 : 
    WB.andw (pack'R_t ws1) (pack'R_t ws2) = pack'R_t (map2 WS.andw ws1 ws2).
   proof.
     apply (canRL _ _ _ _ unpack'SK); apply packP => i hi.
     by rewrite get_unpack'S // map2iE // andb'SE // !pack'RbE. 
   qed.

   lemma orb'Ru'SE ws1 ws2 : 
     WB.orw (pack'R_t ws1) (pack'R_t ws2) = pack'R_t (map2 WS.orw ws1 ws2).
   proof.
     apply (canRL _ _ _ _ unpack'SK); apply packP => i hi.
     by rewrite get_unpack'S // map2iE // orb'SE // !pack'RbE. 
   qed.

   lemma xorb'Ru'SE ws1 ws2 : 
     WB.(+^) (pack'R_t ws1) (pack'R_t ws2) = pack'R_t (map2 WS.(+^) ws1 ws2).
   proof.
     apply (canRL _ _ _ _ unpack'SK); apply packP => i hi.
     by rewrite get_unpack'S // map2iE // xorb'SE // !pack'RbE. 
   qed.

   lemma bits'S_div (w:WB.t) i : 0 <= i =>
     w \bits'S i = WS.of_int (WB.to_uint w %/ (2^(sizeS*i))).
   proof.
     move=> hi;apply WS.to_uintRL;rewrite -bits_divmod.
     + smt (WS.gt0_size). smt (WS.gt0_size).
     rewrite to_uint_bits; congr; rewrite WS.bitsE WB.bitsE; apply eq_in_mkseq.
     by move=> k hk /=;rewrite bits'SiE 1:// mulzC.
   qed.

   lemma of_int_bits'S_div w i : 0 <= i < r =>
     (WB.of_int w) \bits'S i = WS.of_int (w %/ (2^(sizeS*i))).
   proof. 
     move=> [h0i hir];rewrite bits'S_div //.
     rewrite WB.of_uintK modz_pow2_div. 
     + by rewrite sizeBrS mulzC; apply cmpW; apply mulz_cmp_r.
     rewrite -WS.of_int_mod modz_mod_pow2 /min.
     have -> /= : !sizeB - sizeS * i < sizeS.
     + rewrite sizeBrS.
       have -> : r * sizeS - sizeS * i = sizeS * (r - i) by ring.
       by rewrite -lezNgt;apply ler_pemulr;[ apply ltzW | smt ()].
     by rewrite WS.of_int_mod.
   qed.
 
   hint simplify (pack'RwE, bits'SiE, pack'RbE, get_unpack'S, unpack'SK, pack'RK, 
                  mapbE, map2bE, andb'SE, orb'SE, xorb'SE,
                  andb'Ru'SE, orb'Ru'SE, xorb'Ru'SE).

   lemma to_uint_zeroextu'B (w:WS.t) :
     WB.to_uint (zeroextu'B w) = WS.to_uint w.
   proof.
     rewrite /zeroextu'B WB.of_uintK modz_small //. 
     apply bound_abs;have [h1 h2] := WS.to_uint_cmp w;split => // ?.
     apply: (ltr_le_trans (2^sizeS)) => //.
     apply pow_Mle;smt (le_size WS.gt0_size).
   qed.

   lemma zeroextu'B_bit (w:WS.t) i: (zeroextu'B w).[i] = ((0 <= i < sizeS) /\ w.[i]).
   proof.
     rewrite /zeroextu'B WB.of_intwE /WB.int_bit (modz_small (to_uint w)).
     + smt(gt0_r WS.gt0_size sizeBrS pow_Mle WS.to_uint_cmp).
     have -> := WS.get_to_uint w i.
     case: (0 <= i < sizeS) => hi /=;1: smt(gt0_r WS.gt0_size sizeBrS).
     have [ /#| h]: (i < 0 \/ sizeS <= i) by smt().
     rewrite divz_small 2://.
     smt(gt0_r WS.gt0_size sizeBrS pow_Mle WS.to_uint_cmp).
   qed.

   lemma to_uint_truncateu'S (w:WB.t) :
     WS.to_uint (truncateu'S w) = WB.to_uint w %% 2 ^ sizeS.
   proof. by rewrite /truncateu'S WS.of_uintK. qed.

   lemma zeroext_truncateu'S_and (w:WB.t) :
     zeroextu'B (truncateu'S w) = andw w (WB.of_int (2^sizeS - 1)).
   proof. 
     rewrite WB.and_mod; 1: smt (le_size WS.gt0_size).
     rewrite -(WB.to_uintK (zeroextu'B (truncateu'S w))).
     by rewrite to_uint_zeroextu'B to_uint_truncateu'S. 
   qed.

   lemma of_uint_pack'R i : 
      (WB.of_int i) = 
        pack'R (map (fun k => WS.of_int ((i %/ 2^(sizeS * k)) %% 2^sizeS)) (iota_ 0 r)).
   proof.
     rewrite -(unpack'SK (WB.of_int i)) /unpack'S Pack.init_of_list. 
     do 2! congr; apply (eq_from_nth (WS.of_int 0)) => [ | k]; rewrite !size_map //.
     move=> hk;rewrite !(nth_map 0) //=.
     move: hk;rewrite size_iota /max gt0_r /= => hk;rewrite !nth_iota //=.
     case: hk => hk1 hk2;rewrite bits'S_div //.
     rewrite WB.of_uintK -(WS.of_int_mod (i %% 2 ^ sizeB %/ 2 ^ (sizeS * k))).
     congr;rewrite modz_pow2_div 1://.
     + by rewrite sizeBrS; smt (WS.gt0_size).
     rewrite modz_dvd 2://;apply dvdz_exp2l.
     rewrite sizeBrS (_: r * sizeS - sizeS * k = sizeS * (r - k)); 1: by ring.
     split; 1: smt (WS.gt0_size).
     by move=> ?;apply ler_pemulr => // /#.
   qed.

   op x86_VPADD_'Ru'S (w1 : WB.t) (w2:WB.t) = 
     map2 WS.(+) w1 w2.

(*   op x86_VPSUB_'Ru'S (w1 : WB.t) (w2:WB.t) = 
     map2 (fun (x y:WS.t) => x - y) w1 w2.

   op x86_VPMUL_'Ru'S (w1 : WB.t) (w2:WB.t) = 
     map2 WS.( * ) w1 w2. *)

   op x86_VPSLL_'Ru'S (w : WB.t) (cnt : W8.t) = 
     map (fun (w:WS.t) => w `<<` cnt) w.

   op x86_VPSRL_'Ru'S (w : WB.t) (cnt : W8.t) = 
     map (fun (w:WS.t) => w `>>` cnt) w.

   op x86_VPBROADCAST_'Ru'S (w: WS.t) = 
     pack'R (map (fun i => w) (iota_ 0 r)).

   lemma x86_'Ru'S_rol_xor i w : 0 < i < sizeS => 
      x86_VPSLL_'Ru'S w (W8.of_int i) +^ x86_VPSRL_'Ru'S w (W8.of_int (sizeS - i)) =
      map (fun w0 => WS.rol w0 i) w.
   proof.
     move=> hr;rewrite /x86_VPSRL_'Ru'S /x86_VPSLL_'Ru'S.
     rewrite /map;apply wordP => j hj.
     by rewrite xorb'SE !pack'RbE 1..3:// !initiE 1..3:// /= rol_xor_shft.
   qed.

   lemma x86_'Ru'S_rol_xor_red w1 w2 i si: 
     w1 = w2 => W8.to_uint si = sizeS - W8.to_uint i => 0 < W8.to_uint i < sizeS =>
     x86_VPSLL_'Ru'S w1 i +^ x86_VPSRL_'Ru'S w2 si =
     map (fun w0 => WS.rol w0 (W8.to_uint i)) w1.
   proof.
     by move=> -> hsi hi; rewrite -(W8.to_uintK i) -(W8.to_uintK si) hsi x86_'Ru'S_rol_xor.
   qed.

   hint simplify x86_'Ru'S_rol_xor_red.

end W_WS.

abstract theory BitWordSH.
  op size : int.
  axiom size_le_256 : size <= 256.
  clone include BitWord with op size <- size.

  op (`>>`) (w1 : t) (w2 : W8.t) = w1 `>>>` (to_uint w2 %% size).
  op (`<<`) (w1 : t) (w2 : W8.t) = w1 `<<<` (to_uint w2 %% size). 

  lemma shr_div w1 w2 : to_uint (w1 `>>` w2) = to_uint w1 %/ 2^ (to_uint w2 %% size).
  proof.
    rewrite -{1}(to_uintK w1) /(`>>`) shrDP; 1: smt (modz_cmp gt0_size).
    rewrite of_uintK to_uint_mod modz_small 2://.
    apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
    by have:= to_uint_cmp w1; smt (gt0_pow2).
  qed.

  lemma shr_div_le w1 i : 0 <= i < size => 
     to_uint (w1 `>>` (W8.of_int i)) = to_uint w1 %/ 2^ i.
  proof.
    move=> hi;rewrite shr_div of_uintK.
    rewrite (modz_small i) 1:pow2_8; 1: smt (size_le_256).
    by rewrite modz_small //;apply bound_abs.
  qed.

  lemma rol_xor_shft w i : 0 < i < size => 
    rol w i = (w `<<` W8.of_int i) +^ (w `>>` W8.of_int (size - i)).
  proof.
    move=> hi; rewrite /(`<<`) /(`>>`) !W8.of_uintK.
    have h : 0 <= i < `|W8.modulus|.
    + by rewrite /=; smt (size_le_256).
    rewrite !(modz_small _ W8.modulus) 1:// 1:[smt (size_le_256)] !modz_small 1,2:/#.
    by rewrite rol_xor 1:/#.
  qed.

end BitWordSH.

theory W16.
  abbrev [-printing] size = 16.
  clone include BitWordSH with op size <- size
  proof gt0_size by done,
        size_le_256 by done.
end W16. export W16.

clone export W_WS as W2u8 with 
  op sizeS <- W8.size, op sizeB <- W16.size, op r <- 2, 
  theory WS <- W8, theory WB <- W16
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u8" "'R" as "2" "'S" as "8" "'B" as "16" .

theory W32.
  abbrev [-printing] size = 32.
  clone include BitWordSH with op size <- size
  proof gt0_size by done,
        size_le_256 by done.
end W32. export W32.

clone export W_WS as W4u8 with 
  op sizeS <- W8.size, op sizeB <- W32.size, op r <- 4, 
  theory WS <- W8, theory WB <- W32
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u8" "'R" as "4" "'S" as "8" "'B" as "32". 

clone export W_WS as W2u16 with 
  op sizeS <- W16.size, op sizeB <- W32.size, op r <- 2, 
  theory WS <- W16, theory WB <- W32
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u16" "'R" as "2" "'S" as "16" "'B" as "32". 

theory W64.
  abbrev [-printing] size = 64.
  clone include BitWordSH with op size <- size
  proof gt0_size by done,
        size_le_256 by done.
end W64. export W64.

clone export W_WS as W8u8 with 
  op sizeS <- W8.size, op sizeB <- W64.size, op r <- 8, 
  theory WS <- W8, theory WB <- W64
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "8u8" "'R" as "8" "'S" as "8" "'B" as "64". 

clone export W_WS as W4u16 with 
  op sizeS <- W16.size, op sizeB <- W64.size, op r <- 4, 
  theory WS <- W16, theory WB <- W64
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u16" "'R" as "4" "'S" as "16" "'B" as "64". 

clone export W_WS as W2u32 with 
  op sizeS <- W32.size, op sizeB <- W64.size, op r <- 2, 
  theory WS <- W32, theory WB <- W64
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u32" "'R" as "2" "'S" as "32" "'B" as "64". 

theory W128.
  abbrev [-printing] size = 128.
  clone include BitWordSH with op size <- size
  proof gt0_size by done,
        size_le_256 by done.
end W128. export W128.

clone export W_WS as W16u8 with 
  op sizeS <- W8.size, op sizeB <- W128.size, op r <- 16, 
  theory WS <- W8, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "16u8" "'R" as "16" "'S" as "8" "'B" as "128". 

clone export W_WS as W8u16 with 
  op sizeS <- W16.size, op sizeB <- W128.size, op r <- 8, 
  theory WS <- W16, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "8u16" "'R" as "8" "'S" as "16" "'B" as "128". 

clone export W_WS as W4u32 with 
  op sizeS <- W32.size, op sizeB <- W128.size, op r <- 4, 
  theory WS <- W32, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u32" "'R" as "4" "'S" as "32" "'B" as "128". 

clone export W_WS as W2u64 with 
  op sizeS <- W64.size, op sizeB <- W128.size, op r <- 2, 
  theory WS <- W64, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u64" "'R" as "2" "'S" as "64" "'B" as "128". 

theory W256.
  abbrev [-printing] size = 256.
  clone include BitWordSH with op size <- size
  proof gt0_size by done,
        size_le_256 by done.
end W256. export W256.

clone export W_WS as W32u8 with 
  op sizeS <- W8.size, op sizeB <- W256.size, op r <- 32, 
  theory WS <- W8, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "32u8" "'R" as "32" "'S" as "8" "'B" as "256". 

clone export W_WS as W16u16 with 
  op sizeS <- W16.size, op sizeB <- W256.size, op r <- 16, 
  theory WS <- W16, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "16u16" "'R" as "16" "'S" as "16" "'B" as "256". 

clone export W_WS as W8u32 with 
  op sizeS <- W32.size, op sizeB <- W256.size, op r <- 8, 
  theory WS <- W32, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "8u32" "'R" as "8" "'S" as "32" "'B" as "256". 

clone export W_WS as W4u64 with 
  op sizeS <- W64.size, op sizeB <- W256.size, op r <- 4, 
  theory WS <- W64, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u64" "'R" as "4" "'S" as "64" "'B" as "256". 

clone export W_WS as W2u128 with 
  op sizeS <- W128.size, op sizeB <- W256.size, op r <- 2, 
  theory WS <- W128, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u128" "'R" as "2" "'S" as "128" "'B" as "256". 


(* -------------------------------------------------------------------- *)
(* Word size                                                            *)

type wsize = [
  | W8
  | W16
  | W32
  | W64
  | W128
  | W256
].

op wsize_i (w:wsize) = 
  with w = W8   => 1
  with w = W16  => 2
  with w = W32  => 4
  with w = W64  => 8
  with w = W128 => 16
  with w = W256 => 32.

(* TODO move *)
lemma gt0_wsize_i ws: 0 < wsize_i ws.
proof. by case ws. qed.
hint exact : gt0_wsize_i.

lemma div_le_wsize ws1 ws2 : wsize_i ws1 <= wsize_i ws2 => wsize_i ws1 %| wsize_i ws2.
proof. by case: ws1 ws2 => -[]. qed.

lemma div_wsize_modulus ws : wsize_i ws %| W64.modulus.
proof. by case ws. qed.
hint exact : div_wsize_modulus.

(*
lemma foo (x y:W128.t) (x1 x2 y1 y2:W64.t):
  x = pack2 [x1; x2] =>
  y = pack2 [y1; y2] =>
  map2 W64.( + ) x y = pack2 [x1 + y1; x2 + y2].
proof. by move=> -> -> /=. qed.

op bits_eq (w:W128.t) xs = 
  all (fun (ix:int * W64.t) => w \bits64 ix.`1 = ix.`2) 
    (zip (iota_ 0 (size xs)) xs).

lemma foo1 (x y:W128.t) (x0 x1 y0 y1:W64.t):
   (bits_eq x [x0; x1]) => 
   (bits_eq y [y0; y1]) =>
   (bits_eq (map2 W64.( + ) x y) [x0 + y0; x1 + y1]).
proof. rewrite /bits_eq /= => />. qed.

lemma foo (x y:W128.t) (x1 x2 y1 y2:W64.t):
  x = pack2 [x1; x2] =>
  y = pack2 [y1; y2] =>
  x `|` y = pack2 [x1 `|` y1; x2 `|` y2].
proof. move=> -> -> /=.
*)

lemma divmod_mul n d i j : 
  0 < n => 
  0 <= j < d =>  
  (i * d + j) %/ (n * d) = i%/ n /\ (i * d + j) %% (n * d) = i %% n * d + j.
proof.
  move=> hn hj.
  have -> : i * d + j = (i %/ n) * (n * d) + (d * (i %% n) + j).
  + have [h1 h2]:= edivzP i n.
    by rewrite {1 2} h1 divzMDl 1:/# (divz_small (i%%n) n) 1:/# /=; ring.
  rewrite divzMDl 1:/# modzMDl.
  have hb: 0 <= d * (i %% n) + j < `|n * d|. 
  + have := modz_cmp i n hn.
    have -> : `|n * d| = n * d by smt().
    have -> h : n * d = (n-1) * d + d by ring.
    split;1: smt(); move=> ?. 
    apply ler_lt_add; 2:smt().
    by rewrite mulzC ler_pmul2r /#.
  by rewrite (divz_small _ (n*d)) 1://  (modz_small _ (n*d)) 1:// /=; ring.
qed.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits8                                                                  *)
(* --------------------------------------------------------------------------------- *)

lemma bits8_W2u16 ws i : 
  W2u16.pack2_t ws \bits8 i = if 0 <= i < 4 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 4) => /= hi; last by rewrite W32.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 8 i j _ hj; 1 :done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u16_red ws i : 
  0 <= i < 4 => W2u16.pack2_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W2u16 h. qed.

lemma bits8_W4u16 ws i : 
  W4u16.pack4_t ws \bits8 i = if 0 <= i < 8 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 8) => /= hi; last by rewrite W64.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 2 8 i j _ hj; 1:done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W4u16_red ws i : 
  0 <= i < 8 => W4u16.pack4_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W4u16 h. qed.

lemma bits8_W8u16 ws i : 
  W8u16.pack8_t ws \bits8 i = if 0 <= i < 16 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 16) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack8wE 1:/#; have [-> ->] := divmod_mul 2 8 i j _ hj; 1: done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W8u16_red ws i : 
  0 <= i < 16 => W8u16.pack8_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W8u16 h. qed.

lemma bits8_W16u16 ws i : 
  W16u16.pack16_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack16wE 1:/#; have [-> ->] := divmod_mul 2 8 i j _ hj; 1: done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W16u16_red ws i : 
  0 <= i < 32 => W16u16.pack16_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W16u16 h. qed.

hint simplify bits8_W2u16_red, bits8_W4u16_red, bits8_W8u16_red, bits8_W16u16_red.

lemma bits8_W2u32 ws i : 
  W2u32.pack2_t ws \bits8 i = if 0 <= i < 8 then ws.[i%/4] \bits8 (i%%4) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 8) => /= hi; last by rewrite W64.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 4 8 i j _ hj; 1: done; rewrite W4u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u32_red ws i : 
  0 <= i < 8 => W2u32.pack2_t ws \bits8 i = ws.[i%/4] \bits8 (i%%4).
proof. by move=> h;rewrite bits8_W2u32 h. qed.

lemma bits8_W4u32 ws i : 
  W4u32.pack4_t ws \bits8 i = if 0 <= i < 16 then ws.[i%/4] \bits8 (i%%4) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 16) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 4 8 i j _ hj; 1: done; rewrite W4u8.bits8iE 1:// /#.
qed.

lemma bits8_W4u32_red ws i : 
  0 <= i < 16 => W4u32.pack4_t ws \bits8 i = ws.[i%/4] \bits8 (i%%4).
proof. by move=> h;rewrite bits8_W4u32 h. qed.

lemma bits8_W8u32 ws i : 
  W8u32.pack8_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/4] \bits8 (i%%4) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack8wE 1:/#; have /= [-> ->] := divmod_mul 4 8 i j _ hj; 1: done; rewrite W4u8.bits8iE 1:// /#.
qed.

lemma bits8_W8u32_red ws i : 
  0 <= i < 32 => W8u32.pack8_t ws \bits8 i = ws.[i%/4] \bits8 (i%%4).
proof. by move=> h;rewrite bits8_W8u32 h. qed.

hint simplify bits8_W2u32_red, bits8_W4u32_red, bits8_W8u32_red.

lemma bits8_W2u64 ws i : 
  W2u64.pack2_t ws \bits8 i = if 0 <= i < 16 then ws.[i%/8] \bits8 (i%%8) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 16) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 8 8 i j _ hj; 1: done; rewrite W8u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u64_red ws i : 
  0 <= i < 16 => W2u64.pack2_t ws \bits8 i = ws.[i%/8] \bits8 (i%%8).
proof. by move=> h;rewrite bits8_W2u64 h. qed.

lemma bits8_W4u64 ws i : 
  W4u64.pack4_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/8] \bits8 (i%%8) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 8 8 i j _ hj; 1: done; rewrite W8u8.bits8iE 1:// /#.
qed.

lemma bits8_W4u64_red ws i : 
  0 <= i < 32 => W4u64.pack4_t ws \bits8 i = ws.[i%/8] \bits8 (i%%8).
proof. by move=> h;rewrite bits8_W4u64 h. qed.

hint simplify bits8_W2u64_red, bits8_W4u64_red.

lemma bits8_W2u128 ws i : 
  W2u128.pack2_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/16] \bits8 (i%%16) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://. 
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 16 8 i j _ hj; 1: done; rewrite W16u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u128_red ws i : 
  0 <= i < 32 => W2u128.pack2_t ws \bits8 i = ws.[i%/16] \bits8 (i%%16).
proof. by move=> h;rewrite bits8_W2u128 h. qed.

hint simplify bits8_W2u128_red.

lemma W32_bits16_bits8 (w:W32.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

lemma W64_bits16_bits8 (w:W64.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

lemma W128_bits16_bits8 (w:W128.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

lemma W256_bits16_bits8 (w:W256.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

hint simplify W32_bits16_bits8, W64_bits16_bits8, W128_bits16_bits8, W256_bits16_bits8.

lemma W64_bits32_bits8 (w:W64.t) i j: 0 <= j < 4 => w \bits32 i \bits8 j = w \bits8 (4 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W128_bits32_bits8 (w:W128.t) i j: 0 <= j < 4 => w \bits32 i \bits8 j = w \bits8 (4 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W256_bits32_bits8 (w:W256.t) i j: 0 <= j < 4 => w \bits32 i \bits8 j = w \bits8 (4 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

hint simplify W64_bits32_bits8, W128_bits32_bits8, W256_bits32_bits8.
 
lemma W128_bits64_bits8 (w:W128.t) i j: 0 <= j < 8 => w \bits64 i \bits8 j = w \bits8 (8 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits64_bits8 (w:W256.t) i j: 0 <= j < 8 => w \bits64 i \bits8 j = w \bits8 (8 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

hint simplify W128_bits64_bits8, W256_bits64_bits8.

lemma W256_bits128_bits8 (w:W256.t) i j: 0 <= j < 8 => w \bits128 i \bits8 j = w \bits8 (16 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W256_bits128_bits8.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits16                                                                  *)
(* --------------------------------------------------------------------------------- *)
  
lemma bits16_W4u8 ws i : 
  W4u8.pack4_t ws \bits16 i = if 0 <= i < 2 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W32_bits16_bits8 1://.
  case: (0 <= i < 2) => hi; last by rewrite W2u8.get_zero W4u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W4u8.pack4bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W4u8_red ws i : 
  0 <= i < 2 => W4u8.pack4_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W4u8 h. qed.

lemma bits16_W8u8 ws i : 
  W8u8.pack8_t ws \bits16 i = if 0 <= i < 4 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W64_bits16_bits8 1://.
  case: (0 <= i < 4) => hi; last by rewrite W2u8.get_zero W8u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W8u8.pack8bE 1:/#.
  have []-> //: j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W8u8_red ws i : 
  0 <= i < 4 => W8u8.pack8_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W8u8 h. qed.

lemma bits16_W16u8 ws i : 
  W16u8.pack16_t ws \bits16 i = if 0 <= i < 8 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W128_bits16_bits8 1://.
  case: (0 <= i < 8) => hi; last by rewrite W2u8.get_zero W16u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W16u8.pack16bE 1:/#.
  have []-> //: j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W16u8_red ws i : 
  0 <= i < 8 => W16u8.pack16_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W16u8 h. qed.

lemma bits16_W32u8 ws i : 
  W32u8.pack32_t ws \bits16 i = if 0 <= i < 16 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W256_bits16_bits8 1://.
  case: (0 <= i < 16) => hi; last by rewrite W2u8.get_zero W32u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W32u8.pack32bE 1:/#.
  have []-> //: j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W32u8_red ws i : 
  0 <= i < 16 => W32u8.pack32_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W32u8 h. qed.

hint simplify bits16_W4u8_red, bits16_W8u8_red, bits16_W16u8_red, bits16_W32u8.

lemma bits16_W2u32 ws i : 
  W2u32.pack2_t ws \bits16 i = if 0 <= i < 4 then ws.[i%/2] \bits16 (i%%2) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://. 
  case: (0 <= i < 4) => /= hi; last by rewrite W64.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 16 i j _ hj; 1: done; rewrite W2u16.bits16iE 1:// /#.
qed.

lemma bits16_W2u32_red ws i : 
  0 <= i < 4 => W2u32.pack2_t ws \bits16 i = ws.[i%/2] \bits16 (i%%2).
proof. by move=> h;rewrite bits16_W2u32 h. qed.

lemma bits16_W4u32 ws i : 
  W4u32.pack4_t ws \bits16 i = if 0 <= i < 8 then ws.[i%/2] \bits16 (i%%2) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://. 
  case: (0 <= i < 8) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 2 16 i j _ hj; 1: done; rewrite W2u16.bits16iE 1:// /#.
qed.

lemma bits16_W4u32_red ws i : 
  0 <= i < 8 => W4u32.pack4_t ws \bits16 i = ws.[i%/2] \bits16 (i%%2).
proof. by move=> h;rewrite bits16_W4u32 h. qed.

lemma bits16_W8u32 ws i : 
  W8u32.pack8_t ws \bits16 i = if 0 <= i < 16 then ws.[i%/2] \bits16 (i%%2) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://. 
  case: (0 <= i < 16) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack8wE 1:/#; have /= [-> ->] := divmod_mul 2 16 i j _ hj; 1: done; rewrite W2u16.bits16iE 1:// /#.
qed.

lemma bits16_W8u32_red ws i : 
  0 <= i < 16 => W8u32.pack8_t ws \bits16 i = ws.[i%/2] \bits16 (i%%2).
proof. by move=> h;rewrite bits16_W8u32 h. qed.
  
hint simplify bits16_W2u32_red, bits16_W4u32_red, bits16_W8u32_red.

lemma bits16_W2u64 ws i : 
  W2u64.pack2_t ws \bits16 i = if 0 <= i < 8 then ws.[i%/4] \bits16 (i%%4) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://. 
  case: (0 <= i < 8) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 4 16 i j _ hj; 1: done; rewrite W4u16.bits16iE 1:// /#.
qed.

lemma bits16_W2u64_red ws i : 
  0 <= i < 8 => W2u64.pack2_t ws \bits16 i = ws.[i%/4] \bits16 (i%%4).
proof. by move=> h;rewrite bits16_W2u64 h. qed.

lemma bits16_W4u64 ws i : 
  W4u64.pack4_t ws \bits16 i = if 0 <= i < 16 then ws.[i%/4] \bits16 (i%%4) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://. 
  case: (0 <= i < 16) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 4 16 i j _ hj; 1: done; rewrite W4u16.bits16iE 1:// /#.
qed.

lemma bits16_W4u64_red ws i : 
  0 <= i < 16 => W4u64.pack4_t ws \bits16 i = ws.[i%/4] \bits16 (i%%4).
proof. by move=> h;rewrite bits16_W4u64 h. qed.

hint simplify bits16_W2u64_red, bits16_W4u64_red.

lemma bits16_W2u128 ws i : 
  W2u128.pack2_t ws \bits16 i = if 0 <= i < 16 then ws.[i%/8] \bits16 (i%%8) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://. 
  case: (0 <= i < 16) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 8 16 i j _ hj; 1: done; rewrite W8u16.bits16iE 1:// /#.
qed.

lemma bits16_W2u128_red ws i : 
  0 <= i < 16 => W2u128.pack2_t ws \bits16 i = ws.[i%/8] \bits16 (i%%8).
proof.  by move=> h;rewrite bits16_W2u128 h. qed.

hint simplify bits16_W2u128_red.

lemma W64_bits32_bits16 (w:W64.t) i j: 0 <= j < 2 => w \bits32 i \bits16 j = w \bits16 (2 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W128_bits32_bits16 (w:W128.t) i j: 0 <= j < 2 => w \bits32 i \bits16 j = w \bits16 (2 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W256_bits32_bits16 (w:W256.t) i j: 0 <= j < 2 => w \bits32 i \bits16 j = w \bits16 (2 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

hint simplify W64_bits32_bits16, W128_bits32_bits16, W256_bits32_bits16. 

lemma W128_bits64_bits16 (w:W128.t) i j: 0 <= j < 4 => w \bits64 i \bits16 j = w \bits16 (4 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits64_bits16 (w:W256.t) i j: 0 <= j < 4 => w \bits64 i \bits16 j = w \bits16 (4 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits128_bits16 (w:W256.t) i j: 0 <= j < 8 => w \bits128 i \bits16 j = w \bits16 (8 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W128_bits64_bits16, W256_bits64_bits16, W256_bits128_bits16.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits32                                                                  *)
(* --------------------------------------------------------------------------------- *)
  
lemma bits32_W8u8 ws i : 
  W8u8.pack8_t ws \bits32 i = 
    if 0 <= i < 2 then W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W32.zero.
proof.
  apply W4u8.wordP => j hj.
  rewrite W64_bits32_bits8 1://.
  case: (0 <= i < 2) => hi; last by rewrite W4u8.get_zero W8u8.get_out 1:/#.
  rewrite /= W4u8.pack4bE 1:// /= W8u8.pack8bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits32_W8u8_red ws i : 
  0 <= i < 2 =>
  W8u8.pack8_t ws \bits32 i = 
    W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits32_W8u8 h. qed.

lemma bits32_W16u8 ws i : 
  W16u8.pack16_t ws \bits32 i = 
    if 0 <= i < 4 then W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W32.zero.
proof.
  apply W4u8.wordP => j hj.
  rewrite W128_bits32_bits8 1://.
  case: (0 <= i < 4) => hi; last by rewrite W4u8.get_zero W16u8.get_out 1:/#.
  rewrite /= W4u8.pack4bE 1:// /= W16u8.pack16bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits32_W16u8_red ws i : 
  0 <= i < 4 =>
  W16u8.pack16_t ws \bits32 i = 
    W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits32_W16u8 h. qed.

lemma bits32_W32u8 ws i : 
  W32u8.pack32_t ws \bits32 i = 
    if 0 <= i < 8 then W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W32.zero.
proof.
  apply W4u8.wordP => j hj.
  rewrite W256_bits32_bits8 1://.
  case: (0 <= i < 8) => hi; last by rewrite W4u8.get_zero W32u8.get_out 1:/#.
  rewrite /= W4u8.pack4bE 1:// /= W32u8.pack32bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits32_W32u8_red ws i : 
  0 <= i < 8 =>
  W32u8.pack32_t ws \bits32 i = 
    W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits32_W32u8 h. qed.

hint simplify bits32_W8u8_red, bits32_W16u8_red, bits32_W32u8_red.

lemma bits32_W4u16 ws i : 
  W4u16.pack4_t ws \bits32 i = 
    if 0 <= i < 2 then W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W32.zero.
proof.
  apply W2u16.wordP => j hj.
  rewrite W64_bits32_bits16 1://.
  case: (0 <= i < 2) => hi; last by rewrite W2u16.get_zero W4u16.get_out 1:/#.
  rewrite /= W2u16.pack2bE 1:// /= W4u16.pack4bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits32_W4u16_red ws i : 
  0 <= i < 2 => 
  W4u16.pack4_t ws \bits32 i = W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits32_W4u16 h. qed.

lemma bits32_W8u16 ws i : 
  W8u16.pack8_t ws \bits32 i = 
    if 0 <= i < 4 then W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W32.zero.
proof.
  apply W2u16.wordP => j hj.
  rewrite W128_bits32_bits16 1://.
  case: (0 <= i < 4) => hi; last by rewrite W2u16.get_zero W8u16.get_out 1:/#.
  rewrite /= W2u16.pack2bE 1:// /= W8u16.pack8bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits32_W8u16_red ws i : 
  0 <= i < 4 =>
  W8u16.pack8_t ws \bits32 i = W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits32_W8u16 h. qed.

lemma bits32_W16u16 ws i : 
  W16u16.pack16_t ws \bits32 i = 
    if 0 <= i < 8 then W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W32.zero.
proof.
  apply W2u16.wordP => j hj.
  rewrite W256_bits32_bits16 1://.
  case: (0 <= i < 8) => hi; last by rewrite W2u16.get_zero W16u16.get_out 1:/#.
  rewrite /= W2u16.pack2bE 1:// /= W16u16.pack16bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits32_W16u16_red ws i : 
  0 <= i < 8 => 
  W16u16.pack16_t ws \bits32 i = W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits32_W16u16 h. qed.

hint simplify bits32_W4u16_red, bits32_W8u16_red, bits32_W16u16_red.

lemma bits32_W2u64 ws i :
  W2u64.pack2_t ws \bits32 i = if 0 <= i < 4 then ws.[i%/2] \bits32 (i%%2) else W32.zero.
proof.
  apply W32.wordP => j hj; rewrite !bits32iE 1,2://. 
  case: (0 <= i < 4) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 32 i j _ hj; 1: done; rewrite W2u32.bits32iE 1:// /#.
qed.

lemma bits32_W2u64_red ws i :
  0 <= i < 4 => W2u64.pack2_t ws \bits32 i = ws.[i%/2] \bits32 (i%%2).
proof. by move=> h;rewrite bits32_W2u64 h. qed.

lemma bits32_W4u64 ws i :
  W4u64.pack4_t ws \bits32 i = if 0 <= i < 8 then ws.[i%/2] \bits32 (i%%2) else W32.zero.
proof.
  apply W32.wordP => j hj; rewrite !bits32iE 1,2://. 
  case: (0 <= i < 8) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 2 32 i j _ hj; 1: done; rewrite W2u32.bits32iE 1:// /#.
qed.

lemma bits32_W4u64_red ws i :
  0 <= i < 8 => W4u64.pack4_t ws \bits32 i = ws.[i%/2] \bits32 (i%%2).
proof. by move=> h;rewrite bits32_W4u64 h. qed.

hint simplify bits32_W2u64_red, bits32_W4u64_red.

lemma bits32_W2u128 ws i :
  W2u128.pack2_t ws \bits32 i = if 0 <= i < 8 then ws.[i%/4] \bits32 (i%%4) else W32.zero.
proof.
  apply W32.wordP => j hj; rewrite !bits32iE 1,2://. 
  case: (0 <= i < 8) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 4 32 i j _ hj; 1: done; rewrite W4u32.bits32iE 1:// /#.
qed.

lemma bits32_W2u128_red ws i :
  0 <= i < 8 => W2u128.pack2_t ws \bits32 i = ws.[i%/4] \bits32 (i%%4).
proof. by move=> h;rewrite bits32_W2u128 h. qed.

hint simplify bits32_W2u128_red.

lemma W128_bits64_bits32 (w:W128.t) i j: 0 <= j < 2 => w \bits64 i \bits32 j = w \bits32 (2 * i + j).
proof.
  move=> hj; apply W32.wordP => k hk.
  by rewrite !bits32iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits64_bits32 (w:W256.t) i j: 0 <= j < 2 => w \bits64 i \bits32 j = w \bits32 (2 * i + j).
proof.
  move=> hj; apply W32.wordP => k hk.
  by rewrite !bits32iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits128_bits32 (w:W256.t) i j: 0 <= j < 4 => w \bits128 i \bits32 j = w \bits32 (4 * i + j).
proof.
  move=> hj; apply W32.wordP => k hk.
  by rewrite !bits32iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W128_bits64_bits32, W256_bits64_bits32, W256_bits128_bits32.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits64                                                                 *)
(* --------------------------------------------------------------------------------- *)

lemma bits64_W16u8 ws i : 
  W16u8.pack16_t ws \bits64 i = 
    if 0 <= i < 2 then W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                                   ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]]
    else W64.zero.
proof.
  apply W8u8.wordP => j hj.
  rewrite W128_bits64_bits8 1://.
  case: (0 <= i < 2) => hi; last by rewrite W8u8.get_zero W16u8.get_out 1:/#.
  rewrite /= W8u8.pack8bE 1:// /= W16u8.pack16bE 1:/#.
  by move: hj; rewrite -(mema_iota 0 8) /= => -[|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma bits64_W16u8_red ws i : 
  0 <= i < 2 =>
  W16u8.pack16_t ws \bits64 i = 
    W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]].
proof. by move=> h;rewrite bits64_W16u8 h. qed.

lemma bits64_W32u8 ws i : 
  W32u8.pack32_t ws \bits64 i = 
    if 0 <= i < 4 then W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                                   ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]]
    else W64.zero.
proof.
  apply W8u8.wordP => j hj.
  rewrite W256_bits64_bits8 1://.
  case: (0 <= i < 4) => hi; last by rewrite W8u8.get_zero W32u8.get_out 1:/#.
  rewrite /= W8u8.pack8bE 1:// /= W32u8.pack32bE 1:/#.
  by move: hj; rewrite -(mema_iota 0 8) /= => -[|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma bits64_W32u8_red ws i : 
  0 <= i < 4 =>
  W32u8.pack32_t ws \bits64 i = 
    W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]].
proof. by move=> h;rewrite bits64_W32u8 h. qed.

hint simplify bits64_W16u8_red, bits64_W32u8_red.

lemma bits64_W8u16 ws i : 
  W8u16.pack8_t ws \bits64 i = 
    if 0 <= i < 2 then W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W64.zero.
proof.
  apply W4u16.wordP => j hj.
  rewrite W128_bits64_bits16 1://.
  case: (0 <= i < 2) => hi; last by rewrite W4u16.get_zero W8u16.get_out 1:/#.
  rewrite /= W4u16.pack4bE 1:// /= W8u16.pack8bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits64_W8u16_red ws i : 
  0 <= i < 2 => 
  W8u16.pack8_t ws \bits64 i = 
    W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits64_W8u16 h. qed.

lemma bits64_W16u16 ws i : 
  W16u16.pack16_t ws \bits64 i = 
    if 0 <= i < 4 then W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W64.zero.
proof.
  apply W4u16.wordP => j hj.
  rewrite W256_bits64_bits16 1://.
  case: (0 <= i < 4) => hi; last by rewrite W4u16.get_zero W16u16.get_out 1:/#.
  rewrite /= W4u16.pack4bE 1:// /= W16u16.pack16bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits64_W16u16_red ws i : 
  0 <= i < 4 => 
  W16u16.pack16_t ws \bits64 i = 
    W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits64_W16u16 h. qed.

hint simplify bits64_W8u16_red, bits64_W16u16_red.

lemma bits64_W4u32 ws i :
  W4u32.pack4_t ws \bits64 i = 
    if 0 <= i < 2 then W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W64.zero.
proof.
  apply W2u32.wordP => j hj.
  rewrite W128_bits64_bits32 1://.
  case: (0 <= i < 2) => hi; last by rewrite W2u32.get_zero W4u32.get_out 1:/#.
  rewrite /= W2u32.pack2bE 1:// /= W4u32.pack4bE 1:/#.
  by have [|]-> : j = 0 \/ j = 1 by smt().
qed.  

lemma bits64_W4u32_red ws i :
  0 <= i < 2 =>
  W4u32.pack4_t ws \bits64 i = W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits64_W4u32 h. qed.

lemma bits64_W8u32 ws i :
  W8u32.pack8_t ws \bits64 i = 
    if 0 <= i < 4 then W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W64.zero.
proof.
  apply W2u32.wordP => j hj.
  rewrite W256_bits64_bits32 1://.
  case: (0 <= i < 4) => hi; last by rewrite W2u32.get_zero W8u32.get_out 1:/#.
  rewrite /= W2u32.pack2bE 1:// /= W8u32.pack8bE 1:/#.
  have [|]-> //= : j = 0 \/ j = 1 by smt().
qed.  

lemma bits64_W8u32_red ws i :
  0 <= i < 4 => 
  W8u32.pack8_t ws \bits64 i = W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits64_W8u32 h. qed.

hint simplify bits64_W4u32_red, bits64_W8u32_red.

lemma bits64_W2u128 ws i : 
  W2u128.pack2_t ws \bits64 i = if 0 <= i < 4 then ws.[i%/2] \bits64 (i%%2) else W64.zero.
proof.
  apply W64.wordP => j hj; rewrite !bits64iE 1,2://. 
  case: (0 <= i < 4) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 64 i j _ hj; 1: done; rewrite W2u64.bits64iE 1:// /#.
qed.

lemma bits64_W2u128_red ws i : 
  0 <= i < 4 => W2u128.pack2_t ws \bits64 i = ws.[i%/2] \bits64 (i%%2).
proof. by move=> h;rewrite bits64_W2u128 h. qed.

hint simplify bits64_W2u128_red.

lemma W256_bits128_bits64 (w:W256.t) i j: 0 <= j < 2 => w \bits128 i \bits64 j = w \bits64 (2 * i + j).
proof.
  move=> hj; apply W64.wordP => k hk.
  by rewrite !bits64iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W256_bits128_bits64.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on pack                                                                    *)
(* --------------------------------------------------------------------------------- *)

lemma W2u16_W4u8 ws1 ws2 : 
  pack2 [W2u8.pack2_t ws1; W2u8.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u8.allP => /=. qed.

lemma W4u16_W8u8 ws1 ws2 ws3 ws4 :
  pack4 [W2u8.pack2_t ws1; W2u8.pack2_t ws2; W2u8.pack2_t ws3; W2u8.pack2_t ws4] = 
  pack8 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1]].
proof. by apply W8u8.allP => /=. qed.

lemma W8u16_W16u8 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8:
  pack8 [W2u8.pack2_t ws1; W2u8.pack2_t ws2; W2u8.pack2_t ws3; W2u8.pack2_t ws4;
         W2u8.pack2_t ws5; W2u8.pack2_t ws6; W2u8.pack2_t ws7; W2u8.pack2_t ws8 ] = 
  pack16 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1];
         ws5.[0]; ws5.[1]; ws6.[0]; ws6.[1]; ws7.[0]; ws7.[1]; ws8.[0]; ws8.[1]].
proof. by apply W16u8.allP => /=. qed.

lemma W16u16_W32u8 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15 ws16:
  pack16 [W2u8.pack2_t ws1; W2u8.pack2_t ws2; W2u8.pack2_t ws3; W2u8.pack2_t ws4;
          W2u8.pack2_t ws5; W2u8.pack2_t ws6; W2u8.pack2_t ws7; W2u8.pack2_t ws8;
          W2u8.pack2_t ws9; W2u8.pack2_t ws10; W2u8.pack2_t ws11; W2u8.pack2_t ws12;
          W2u8.pack2_t ws13; W2u8.pack2_t ws14; W2u8.pack2_t ws15; W2u8.pack2_t ws16] = 
  pack32 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1];
          ws5.[0]; ws5.[1]; ws6.[0]; ws6.[1]; ws7.[0]; ws7.[1]; ws8.[0]; ws8.[1];
          ws9.[0]; ws9.[1]; ws10.[0]; ws10.[1]; ws11.[0]; ws11.[1]; ws12.[0]; ws12.[1];
          ws13.[0]; ws13.[1]; ws14.[0]; ws14.[1]; ws15.[0]; ws15.[1]; ws16.[0]; ws16.[1]].
proof. by apply W32u8.allP => /=. qed.

hint simplify W2u16_W4u8, W4u16_W8u8, W8u16_W16u8, W16u16_W32u8.

lemma W2u32_W8u8 ws1 ws2 : 
  pack2 [W4u8.pack4_t ws1; W4u8.pack4_t ws2] = 
  pack8 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]].
proof. by apply W8u8.allP => /=. qed.

lemma W4u32_W16u8 ws1 ws2 ws3 ws4 :
  pack4 [W4u8.pack4_t ws1; W4u8.pack4_t ws2; W4u8.pack4_t ws3; W4u8.pack4_t ws4] = 
  pack16 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3]].
proof. by apply W16u8.allP => /=. qed.

lemma W8u32_W32u8 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8:
  pack8 [W4u8.pack4_t ws1; W4u8.pack4_t ws2; W4u8.pack4_t ws3; W4u8.pack4_t ws4;
         W4u8.pack4_t ws5; W4u8.pack4_t ws6; W4u8.pack4_t ws7; W4u8.pack4_t ws8 ] = 
  pack32 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3];
          ws5.[0]; ws5.[1]; ws5.[2]; ws5.[3]; ws6.[0]; ws6.[1]; ws6.[2]; ws6.[3];
          ws7.[0]; ws7.[1]; ws7.[2]; ws7.[3]; ws8.[0]; ws8.[1]; ws8.[2]; ws8.[3]].
proof. by apply W32u8.allP => /=. qed.

hint simplify W2u32_W8u8, W4u32_W16u8, W8u32_W32u8.

lemma W2u64_W16u8 ws1 ws2:
  pack2 [W8u8.pack8_t ws1; W8u8.pack8_t ws2] = 
  pack16 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws1.[4]; ws1.[5]; ws1.[6]; ws1.[7];
          ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]; ws2.[4]; ws2.[5]; ws2.[6]; ws2.[7]].
proof. by apply W16u8.allP => /=. qed.

lemma W4u64_W32u8 ws1 ws2 ws3 ws4:
  pack4 [W8u8.pack8_t ws1; W8u8.pack8_t ws2; W8u8.pack8_t ws3; W8u8.pack8_t ws4] = 
  pack32 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws1.[4]; ws1.[5]; ws1.[6]; ws1.[7];
          ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]; ws2.[4]; ws2.[5]; ws2.[6]; ws2.[7];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws3.[4]; ws3.[5]; ws3.[6]; ws3.[7];
          ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3]; ws4.[4]; ws4.[5]; ws4.[6]; ws4.[7]].
proof. by apply W32u8.allP => /=. qed.

hint simplify W2u64_W16u8, W4u64_W32u8.

lemma W2u128_W32u8 ws1 ws2:
  pack2 [W16u8.pack16_t ws1; W16u8.pack16_t ws2] = 
  pack32 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws1.[4]; ws1.[5]; ws1.[6]; ws1.[7];
          ws1.[8]; ws1.[9]; ws1.[10]; ws1.[11]; ws1.[12]; ws1.[13]; ws1.[14]; ws1.[15];
          ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]; ws2.[4]; ws2.[5]; ws2.[6]; ws2.[7];
          ws2.[8]; ws2.[9]; ws2.[10]; ws2.[11]; ws2.[12]; ws2.[13]; ws2.[14]; ws2.[15]].
proof. by apply W32u8.allP => /=. qed.

hint simplify W2u128_W32u8.

lemma W2u32_W4u16 ws1 ws2 : 
  pack2 [W2u16.pack2_t ws1; W2u16.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u16.allP => /=. qed.

lemma W4u32_W8u16 ws1 ws2 ws3 ws4 :
  pack4 [W2u16.pack2_t ws1; W2u16.pack2_t ws2; W2u16.pack2_t ws3; W2u16.pack2_t ws4] = 
  pack8 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1]].
proof. by apply W8u16.allP => /=. qed.

lemma W8u32_W16u16 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8:
  pack8 [W2u16.pack2_t ws1; W2u16.pack2_t ws2; W2u16.pack2_t ws3; W2u16.pack2_t ws4;
         W2u16.pack2_t ws5; W2u16.pack2_t ws6; W2u16.pack2_t ws7; W2u16.pack2_t ws8 ] = 
  pack16 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1];
         ws5.[0]; ws5.[1]; ws6.[0]; ws6.[1]; ws7.[0]; ws7.[1]; ws8.[0]; ws8.[1]].
proof. by apply W16u16.allP => /=. qed.

hint simplify W2u32_W4u16, W4u32_W8u16, W8u32_W16u16.

lemma W2u64_W8u16 ws1 ws2:
  pack2 [W4u16.pack4_t ws1; W4u16.pack4_t ws2] = 
  pack8 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3];
         ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]].
proof. by apply W8u16.allP => /=. qed.

lemma W4u64_W16u16 ws1 ws2 ws3 ws4:
  pack4 [W4u16.pack4_t ws1; W4u16.pack4_t ws2; W4u16.pack4_t ws3; W4u16.pack4_t ws4] = 
  pack16 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3]].
proof. by apply W16u16.allP => /=. qed.

hint simplify W2u64_W8u16, W4u64_W16u16.

lemma W2u64_W4u32 ws1 ws2:
  pack2 [W2u32.pack2_t ws1; W2u32.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u32.allP => /=. qed.

lemma W4u64_W8u32 ws1 ws2 ws3 ws4 :
  pack4 [W2u32.pack2_t ws1; W2u32.pack2_t ws2; W2u32.pack2_t ws3; W2u32.pack2_t ws4] = 
  pack8 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1]].
proof. by apply W8u32.allP => /=. qed.

hint simplify W2u64_W4u32, W4u64_W8u32.

lemma W2u128_W4u64 ws1 ws2:
  pack2 [W2u64.pack2_t ws1; W2u64.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u64.allP => /=. qed.

hint simplify W2u128_W4u64.




