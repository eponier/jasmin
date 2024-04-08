open Prog

exception TyError of L.i_loc * string
val ty_lval : Wsize_defs.wsize -> L.i_loc -> lval -> ty
val ty_expr : Wsize_defs.wsize -> L.i_loc -> expr -> ty
val error : Prog.L.i_loc -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val check_prog : Wsize_defs.wsize -> 'asm Sopn.asmOp -> ('info, 'asm) prog -> unit
