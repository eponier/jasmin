From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype ssralg.
From mathcomp Require Import word_ssrZ.

Require Import
  expr
  flag_combination
  sem_type
  shift_kind
  strings
  utils
  wsize.

Require Import
  arch_decl
  arch_utils.

(* --------------------------------------------- *)
Definition riscv_reg_size := U32.
Definition riscv_xreg_size := U64. (* Unused *)

(* -------------------------------------------------------------------- *)
(* Registers. *)
(* According to the RISC-V ABI, X3/GP and X4/TP are unallocatable, so we do not
   model them. *)
#[only(eqbOK)] derive
Variant register : Type :=
| RA  | SP  | X5  | X6  | X7  | X8              (* General-purpose registers. *)
| X9  | X10 | X11 | X12 | X13 | X14 | X15 | X16 (* General-purpose registers. *)
| X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24 (* General-purpose registers. *)
| X25 | X26 | X27 | X28 | X29 | X30 | X31.      (* General-purpose registers. *)

#[ export ]
Instance eqTC_register : eqTypeC register :=
  { ceqP := register_eqb_OK }.

Canonical riscv_register_eqType := @ceqT_eqType _ eqTC_register.

Definition registers :=
  [::  RA;  SP;  X5;  X6;  X7;  X8;
       X9; X10; X11; X12; X13; X14; X15; X16;
      X17; X18; X19; X20; X21; X22; X23; X24;
      X25; X26; X27; X28; X29; X30; X31
  ].


Lemma register_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

#[ export ]
Instance finTC_register : finTypeC register :=
  {
    cenum  := registers;
    cenumP := register_fin_axiom;
  }.

Canonical register_finType := @cfinT_finType _ finTC_register.

Definition register_to_string (r : register) : string :=
  match r with
  | RA  => "ra"
  | SP  => "sp"
  | X5  => "x5"
  | X6  => "x6"
  | X7  => "x7"
  | X8  => "x8"
  | X9  => "x9"
  | X10 => "x10"
  | X11 => "x11"
  | X12 => "x12"
  | X13 => "x13"
  | X14 => "x14"
  | X15 => "x15"
  | X16 => "x16"
  | X17 => "x17"
  | X18 => "x18"
  | X19 => "x19"
  | X20 => "x20"
  | X21 => "x21"
  | X22 => "x22"
  | X23 => "x23"
  | X24 => "x24"
  | X25 => "x25"
  | X26 => "x26"
  | X27 => "x27"
  | X28 => "x28"
  | X29 => "x29"
  | X30 => "x30"
  | X31 => "x31"
  end.

#[ export ]
Instance reg_toS : ToString (sword riscv_reg_size) register :=
  {| category  := "register"
   ; to_string := register_to_string
  |}.


(* -------------------------------------------------------------------- *)
(* Conditions. *)

#[only(eqbOK)] derive
Variant condition_kind :=
| EQ               (* Equal. *)
| NE               (* Not equal. *)
| LT of signedness (* Signed / Unsigned less than. *)
| GE of signedness (* Signed / Unsigned greater than or equal to. *)
.

#[only(eqbOK)] derive
Record condt := {
  cond_kind : condition_kind;
  cond_fst : option register;
  cond_snd : option register;
}.

#[ export ]
Instance eqTC_condt : eqTypeC condt :=
  { ceqP := condt_eqb_OK }.

Canonical condt_eqType := @ceqT_eqType _ eqTC_condt.

(* -------------------------------------------------------------------- *)
(* Dummy Flag combinations. *)

(* TODO: should we fail/return None instead of this dummy? *)
Definition riscv_fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  FCVar0 .

#[global]
Instance riscv_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := riscv_fc_of_cfc;
  }.

(* -------------------------------------------------------------------- *)
(* Architecture declaration. *)

Notation register_ext := empty.
Notation xregister := empty.
Notation rflag := empty.

Definition riscv_check_CAimm (checker : caimm_checker_s) ws (w : word ws) : bool :=
  match checker with
  | CAimmC_none => true
  | CAimmC_riscv_12bits_signed =>
     let i := wsigned w in
     (-2048 <=? i)%Z && (i <=? 2047)%Z
  | CAimmC_riscv_5bits_unsigned =>
     let i := wunsigned w in
     (i <=? 31)%Z
  | CAimmC_arm_shift_amout _ | CAimmC_arm_wencoding _ | CAimmC_arm_0_8_16_24 => false
  end.

#[ export ]
Instance riscv_decl : arch_decl register register_ext xregister rflag condt :=
  { reg_size  := riscv_reg_size
  ; xreg_size := riscv_xreg_size
  ; cond_eqC  := eqTC_condt
  ; toS_r     := reg_toS
  ; toS_rx    := empty_toS sword32
  ; toS_x     := empty_toS sword64
  ; toS_f     := empty_toS sbool
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := SP
  ; ad_fcp := riscv_fcp
  ; check_CAimm := riscv_check_CAimm
  }.

Definition riscv_linux_call_conv : calling_convention :=
{| callee_saved :=
    map ARReg [:: SP; X8; X9; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27 ]
 ; callee_saved_not_bool := erefl true
 ; call_reg_args  := [:: X10; X11; X12; X13; X14; X15; X16; X17 ]
 ; call_xreg_args := [::]
 ; call_reg_ret   := [:: X10; X11]
 ; call_xreg_ret  := [::]
 ; call_reg_ret_uniq := erefl true;
|}.
