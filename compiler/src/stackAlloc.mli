val memory_analysis :
  (unit Conv.coq_tbl -> Format.formatter -> Compiler_util.fun_error -> unit) ->
  debug:bool -> unit Conv.coq_tbl -> 
  Expr._uprog -> Compiler.stack_alloc_oracles

val pp_oracle : unit Conv.coq_tbl -> Expr._uprog -> Format.formatter -> Compiler.stack_alloc_oracles -> unit
