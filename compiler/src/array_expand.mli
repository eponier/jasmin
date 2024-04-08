open Prog

val init_tbl : ('info, 'asm) func -> Sv.t * (Wsize_defs.wsize * var array) Hv.t
