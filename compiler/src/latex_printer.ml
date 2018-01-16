(* * License
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

(* * Pretty-print Jasmin program (concrete syntax) as LATEX fragments *)

open Syntax
open Printer

module F = Format

type ('a, 'b, 'c, 'd) str = ('a, 'b, 'c, 'd, 'd, 'a) CamlinternalFormatBasics.format6

let eol : _ str = "\\\\\n"

let latex cmd fmt arg =
  F.fprintf fmt "\\jasmin%s{%s}" cmd arg

let symbol s fmt () = latex s fmt ""

let kw = latex "kw"
let ptype = latex "type"
let dname = latex "dname"
let arrow = symbol "arrow"
let sharp fmt () = F.fprintf fmt "\\#"
let openbrace fmt () = F.fprintf fmt "\\{"
let closebrace fmt () = F.fprintf fmt "\\}"

let indent fmt d = if d > 0 then latex "indent" fmt (string_of_int d)

let pp_opt p fmt =
  function
  | None -> ()
  | Some x -> p fmt x

let pp_paren p fmt =
  F.fprintf fmt "(%a)" p

let pp_cc =
    pp_opt (fun fmt x -> F.fprintf fmt "%a " kw (match x with `Inline -> "inline" | `Export -> "export"))

let pp_var fmt x =
  F.fprintf fmt "%s" (L.unloc x)

let string_of_wsize w =
  match w with
  | `W8 -> "b8"
  | `W16 -> "b16"
  | `W32 -> "b32"
  | `W64 -> "b64"
  | `W128 -> "b128"
  | `W256 -> "b256"

let string_of_op1 =
  function
  | `Not -> "!"
  | `Neg -> "-"

let string_of_op2 =
  function
  | `Add  -> "+"
  | `Sub  -> "-"
  | `Mul  -> "*"
  | `And  -> "&&"
  | `Or   -> "||"
  | `BAnd -> "&"
  | `BOr  -> "|"
  | `BXOr -> "^"
  | `ShR  -> ">{}>"
  | `ShL  -> "<{}<"
  | `Asr  -> ">{}>s"
  | `Eq   -> "=="
  | `Neq  -> "!="
  | `Lt   -> "<"
  | `Le   -> "<="
  | `Gt   -> ">"
  | `Ge   -> ">="
  | `Lts  -> "<s"
  | `Les  -> "<=s"
  | `Gts  -> ">s"
  | `Ges  -> ">=s"

type prio =
  | Pmin
  | Por
  | Pand
  | Pbwor
  | Pbwxor
  | Pbwand
  | Pcmpeq
  | Pcmp
  | Pshift
  | Padd
  | Pmul
  | Punary
  | Pbang
  | Pmax

let prio_of_op1 =
  function
  | `Not -> Punary
  | `Neg -> Pbang

let prio_of_op2 =
  function
  | `Add | `Sub  -> Padd
  | `Mul  -> Pmul
  | `And  -> Pand
  | `Or   -> Por
  | `BAnd -> Pbwand
  | `BOr  -> Pbwor
  | `BXOr -> Pbwxor
  | `ShR | `ShL | `Asr -> Pshift
  | `Eq | `Neq  -> Pcmpeq
  | `Lt | `Le | `Gt | `Ge
  | `Lts | `Les | `Gts | `Ges
    -> Pcmp

let optparent fmt ctxt prio p =
  if prio < ctxt then F.fprintf fmt "%s" p

let rec pp_expr_rec prio fmt pe =
  match L.unloc pe with
  | PEParens e -> pp_expr_rec prio fmt e
  | PEVar x -> pp_var fmt x
  | PEGet (x, e) -> F.fprintf fmt "%a[%a]" pp_var x pp_expr e
  | PEFetch (ty, x, e) -> F.fprintf fmt "%a[%a + %a]" (pp_opt (pp_paren pp_type)) ty pp_var x pp_expr e
  | PEBool b -> F.fprintf fmt "%s" (if b then "true" else "false")
  | PEInt i -> F.fprintf fmt "%a" Bigint.pp_print i
  | PECall (f, args) -> F.fprintf fmt "%a(%a)" pp_var f (pp_list ", " pp_expr) args
  | PEPrim (f, args) -> F.fprintf fmt "%a%a(%a)" sharp () pp_var f (pp_list ", " pp_expr) args
  | PEOp1 (op, e) ->
    let p = prio_of_op1 op in
    optparent fmt prio p "(";
    F.fprintf fmt "%s %a" (string_of_op1 op) (pp_expr_rec p) e;
    optparent fmt prio p ")"
  | PEOp2 (op, (e, r)) ->
    let p = prio_of_op2 op in
    optparent fmt prio p "(";
    F.fprintf fmt "%a %s %a" (pp_expr_rec p) e (string_of_op2 op) (pp_expr_rec p) r;
    optparent fmt prio p ")"

and pp_type fmt ty =
  match L.unloc ty with
  | TBool -> F.fprintf fmt "%a" ptype "bool"
  | TInt -> F.fprintf fmt "%a" ptype "int"
  | TWord w -> F.fprintf fmt "%a" ptype (string_of_wsize w)
  | TArray (w, e) -> F.fprintf fmt "%a[%a]" ptype (string_of_wsize w) pp_expr e

and pp_expr fmt e = pp_expr_rec Pmin fmt e

let pp_storage fmt s =
  latex "storageclass" fmt
    (match s with
     | `Reg -> "reg"
     | `Stack -> "stack"
     | `Inline -> "inline")

let pp_sto_ty fmt (sto, ty) =
  F.fprintf fmt "%a %a" pp_storage sto pp_type ty

let pp_arg fmt (sty, x) =
  F.fprintf
    fmt
    "%a %a"
    pp_sto_ty sty
    pp_var x

let pp_args fmt (sty, xs) =
  F.fprintf
    fmt
    "%a %a"
    pp_sto_ty sty
    (pp_list ", " pp_var) xs

let pp_rty =
  pp_opt
    (fun fmt tys ->
       F.fprintf fmt " %a %a"
         arrow ()
         (pp_list ", " pp_sto_ty) tys)

let pp_inbraces depth p fmt x =
  openbrace fmt ();
  F.fprintf fmt eol;
  p fmt x;
  F.fprintf fmt eol;
  indent fmt depth;
  closebrace fmt ()

let pp_lv fmt x =
  match L.unloc x with
  | PLIgnore -> F.fprintf fmt "_"
  | PLVar x -> pp_var fmt x
  | PLArray (x, e) -> F.fprintf fmt "%a[%a]" pp_var x pp_expr e
  | PLMem (ty, x, e) -> F.fprintf fmt "%a[%a + %a]" (pp_opt (pp_paren pp_type)) ty pp_var x pp_expr e

let string_of_eqop =
  function
  | `Raw -> "="
  | `Add -> "+="
  | `Sub -> "-="
  | `ShR -> ">{}>s="
  | `Asr -> ">{}>="
  | `ShL -> "<{}<="
  | `BAnd -> "&="
  | `BXOr -> "\\textasciicircum="
  | `BOr  -> "|="
  | `Mul -> "*="

let pp_sidecond fmt =
  F.fprintf fmt " %a %a" kw "if" pp_expr

let rec pp_instr depth fmt p =
  indent fmt depth;
  match L.unloc p with
  | PIArrayInit x -> F.fprintf fmt "%a (%a);" kw "arrayinit" pp_var x
  | PIAssign (lvs, op, e, cnd) ->
    begin match lvs with
    | [] -> ()
    | _ -> F.fprintf fmt "%a %s " (pp_list ", " pp_lv) lvs (string_of_eqop op) end;
    F.fprintf fmt "%a%a;"
      pp_expr e
      (pp_opt pp_sidecond) cnd
  | PIIf (b, th, el) ->
    begin
    F.fprintf fmt "%a %a %a"
      kw "if"
      pp_expr b
      (pp_block depth) th;
    match el with
    | Some el -> F.fprintf fmt " %a %a" kw "else" (pp_block depth) el
    | None -> () end
  | PIFor (i, (d, lo, hi), body) ->
    F.fprintf fmt "%a %a = %a %a %a %a"
      kw "for"
      pp_var i
      pp_expr lo
      kw (match d with `Down -> "downto" | `Up -> "to")
      pp_expr hi
      (pp_inbraces depth (pp_list eol (pp_instr (depth + 1)))) (L.unloc body)
  | PIWhile (pre, b, body) ->
    F.fprintf fmt "%a %a (%a) %a"
      kw "while"
      (pp_opt (pp_block depth)) pre
      pp_expr b
      (pp_opt (pp_block depth)) body

and pp_block depth fmt blk =
  pp_inbraces depth (pp_list eol (pp_instr (depth + 1))) fmt (L.unloc blk)

let pp_funbody fmt { pdb_vars ; pdb_instr ; pdb_ret } =
  List.iter (fun d -> F.fprintf fmt "%a%a;" indent 1 pp_args d; F.fprintf fmt eol) pdb_vars;
  pp_list eol (pp_instr 1) fmt pdb_instr;
  pp_opt (
    fun fmt ret ->
      F.fprintf fmt eol;
      F.fprintf fmt "%a%a %a;"
        indent 1
        kw "return"
        (pp_list ", " pp_var) ret;
  ) fmt pdb_ret

let pp_fundef fmt { pdf_cc ; pdf_name ; pdf_args ; pdf_rty ; pdf_body } =
  F.fprintf
    fmt
    "%a%a %a(%a)%a %a"
    pp_cc pdf_cc
    kw "fn"
    dname (L.unloc pdf_name)
    (pp_list ", " pp_arg) pdf_args
    pp_rty pdf_rty
    (pp_inbraces 0 pp_funbody) pdf_body;
  F.fprintf fmt eol

let pp_param fmt { ppa_ty ; ppa_name ; ppa_init } =
  F.fprintf fmt "%a %a %a = %a;"
    kw "param"
    pp_type ppa_ty
    dname (L.unloc ppa_name)
    pp_expr ppa_init;
  F.fprintf fmt eol

let pp_global fmt { pgd_name ; pgd_val } =
  F.fprintf fmt "%a = %a;"
    dname (L.unloc pgd_name)
    pp_expr pgd_val;
  F.fprintf fmt eol

let pp_pitem fmt pi =
  match L.unloc pi with
  | PFundef f -> pp_fundef fmt f
  | PParam p -> pp_param fmt p
  | PGlobal g -> pp_global fmt g

let pp_prog fmt prog =
  F.fprintf fmt "%a" (pp_list "\n" pp_pitem) prog