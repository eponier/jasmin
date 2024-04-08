open Eqtype
open Utils0

type stack_zero_strategy =
| SZSloop
| SZSloopSCT
| SZSunrolled

(** val stack_zero_strategy_list : stack_zero_strategy list **)

let stack_zero_strategy_list =
  SZSloop :: (SZSloopSCT :: (SZSunrolled :: []))

(** val stack_zero_strategy_beq :
    stack_zero_strategy -> stack_zero_strategy -> bool **)

let stack_zero_strategy_beq x y =
  match x with
  | SZSloop -> (match y with
                | SZSloop -> true
                | _ -> false)
  | SZSloopSCT -> (match y with
                   | SZSloopSCT -> true
                   | _ -> false)
  | SZSunrolled -> (match y with
                    | SZSunrolled -> true
                    | _ -> false)

(** val stack_zero_strategy_eq_dec :
    stack_zero_strategy -> stack_zero_strategy -> bool **)

let stack_zero_strategy_eq_dec x y =
  let b = stack_zero_strategy_beq x y in if b then true else false

(** val stack_zero_strategy_eq_axiom : stack_zero_strategy Equality.axiom **)

let stack_zero_strategy_eq_axiom =
  eq_axiom_of_scheme stack_zero_strategy_beq

(** val stack_zero_strategy_eqMixin :
    stack_zero_strategy Equality.mixin_of **)

let stack_zero_strategy_eqMixin =
  { Equality.op = stack_zero_strategy_beq; Equality.mixin_of__1 =
    stack_zero_strategy_eq_axiom }

(** val stack_zero_strategy_eqType : Equality.coq_type **)

let stack_zero_strategy_eqType =
  Obj.magic stack_zero_strategy_eqMixin
