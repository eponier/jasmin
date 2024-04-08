open Eqtype
open Utils0

type stack_zero_strategy =
| SZSloop
| SZSloopSCT
| SZSunrolled

val stack_zero_strategy_list : stack_zero_strategy list

val stack_zero_strategy_beq :
  stack_zero_strategy -> stack_zero_strategy -> bool

val stack_zero_strategy_eq_dec :
  stack_zero_strategy -> stack_zero_strategy -> bool

val stack_zero_strategy_eq_axiom : stack_zero_strategy Equality.axiom

val stack_zero_strategy_eqMixin : stack_zero_strategy Equality.mixin_of

val stack_zero_strategy_eqType : Equality.coq_type
