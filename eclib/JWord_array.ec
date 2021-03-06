(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap List StdOrder BitEncoding Bool.
(*---*) import Ring.IntID IntOrder BS2Int.
require import JUtils JArray JWord.

abstract theory WArray.

  clone include MonoArray with
    type elem <- W8.t,
    op dfl    <- W8.zero.

  op get8 (t:t) (i:int)  : W8.t = t.[i].

  op get16 (t:t) (i:int) : W16.t =
    pack2_t (W2u8.Pack.init (fun j => t.[2*i + j]))
  axiomatized by get16E.

  op get32 (t:t) (i:int) : W32.t =
    pack4_t (W4u8.Pack.init (fun j => t.[4*i + j]))
  axiomatized by get32E.

  op get64 (t:t) (i:int) : W64.t =
    pack8_t (W8u8.Pack.init (fun j => t.[8*i + j]))
  axiomatized by get64E.

  op get128 (t:t) (i:int) : W128.t =
    pack16_t (W16u8.Pack.init (fun j => t.[16*i + j]))
  axiomatized by get128E.

  op get256 (t:t) (i:int) : W256.t =
    pack32_t (W32u8.Pack.init (fun j => t.[32*i + j]))
  axiomatized by get256E.

  op set8 (t:t) (i:int) (w:W8.t) : t = t.[i <- w].

  op set16 (t:t) (i:int) (w:W16.t) =
    init (fun k => if 2*i <= k < 2*(i+1) then w \bits8 (k - 2*i) else t.[k])
  axiomatized by set16E.

  op set32 (t:t) (i:int) (w:W32.t) =
    init (fun k => if 4*i <= k < 4*(i+1) then w \bits8 (k - 4*i) else t.[k])
  axiomatized by set32E.

  op set64 (t:t) (i:int) (w:W64.t) =
    init (fun k => if 8*i <= k < 8*(i+1) then w \bits8 (k - 8*i) else t.[k])
  axiomatized by set64E.

  op set128 (t:t) (i:int) (w:W128.t) =
    init (fun k => if 16*i <= k < 16*(i+1) then w \bits8 (k - 16*i) else t.[k])
  axiomatized by set128E.

  op set256 (t:t) (i:int) (w:W256.t) =
    init (fun k => if 32*i <= k < 32*(i+1) then w \bits8 (k - 32*i) else t.[k])
  axiomatized by set256E.

  (* ----------------------------------------------------- *)

  lemma get_set8E t x y w:
    0 <= x < size =>
    get8 (set8 t x w) y = if y = x then w else get8 t y.
  proof. apply get_setE. qed.

  lemma get8_set16E t x y w :
    0 <= x => 2*(x + 1) <= WArray.size =>
    get8 (set16 t x w) y = if 2*x <= y < 2*(x+1) then w \bits8 (y - 2*x) else get8 t y.
  proof.
    move=> hx hs; rewrite set16E /get8.
    case: (2 * x <= y < 2 * (x + 1)) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get_set16E t x y w:
    0 <= x => 2*(x + 1) <= WArray.size =>
    get16 (set16 t x w) y = if y = x then w else get16 t y.
  proof.
    move=> hx hs; rewrite set16E !get16E.
    case: (y = x) => [-> | hne].
    + rewrite -(W2u8.unpack8K w);congr.
      apply W2u8.Pack.ext_eq => k hk; rewrite W2u8.get_unpack8 1:// W2u8.Pack.initiE //= initiE //= /#.
    congr; apply W2u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 2 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set32E t x y w :
    0 <= x => 4*(x + 1) <= WArray.size =>
    get8 (set32 t x w) y = if 4*x <= y < 4*(x+1) then w \bits8 (y - 4*x) else get8 t y.
  proof.
    move=> hx hs; rewrite set32E /get8.
    case: (4 * x <= y < 4 * (x + 1)) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get_set32E t x y w:
    0 <= x => 4*(x + 1) <= WArray.size =>
    get32 (set32 t x w) y = if y = x then w else get32 t y.
  proof.
    move=> hx hs; rewrite set32E !get32E.
    case: (y = x) => [-> | hne].
    + rewrite -(W4u8.unpack8K w);congr.
      apply W4u8.Pack.ext_eq => k hk; rewrite W4u8.get_unpack8 //= W4u8.Pack.initiE //= initiE /#.
    congr; apply W4u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 4 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set64E t x y w :
    0 <= x => 8*(x + 1) <= WArray.size =>
    get8 (set64 t x w) y = if 8*x <= y < 8*(x+1) then w \bits8 (y - 8*x) else get8 t y.
  proof.
    move=> hx hs; rewrite set64E /get8.
    case: (8 * x <= y < 8 * (x + 1)) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get_set64E t x y w:
    0 <= x => 8*(x + 1) <= WArray.size =>
    get64 (set64 t x w) y = if y = x then w else get64 t y.
  proof.
    move=> hx hs; rewrite set64E !get64E.
    case: (y = x) => [-> | hne].
    + rewrite -(W8u8.unpack8K w);congr.
      apply W8u8.Pack.ext_eq => k hk; rewrite W8u8.get_unpack8 //= W8u8.Pack.initiE //= initiE /#.
    congr; apply W8u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 8 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set128E t x y w :
    0 <= x => 16*(x + 1) <= WArray.size =>
    get8 (set128 t x w) y = if 16*x <= y < 16*(x+1) then w \bits8 (y - 16*x) else get8 t y.
  proof.
    move=> hx hs; rewrite set128E /get8.
    case: (16 * x <= y < 16 * (x + 1)) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get_set128E t x y w:
    0 <= x => 16*(x + 1) <= WArray.size =>
    get128 (set128 t x w) y = if y = x then w else get128 t y.
  proof.
    move=> hx hs; rewrite set128E !get128E.
    case: (y = x) => [-> | hne].
    + rewrite -(W16u8.unpack8K w);congr.
      apply W16u8.Pack.ext_eq => k hk; rewrite W16u8.get_unpack8 //= W16u8.Pack.initiE //= initiE /#.
    congr; apply W16u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 16 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set256E t x y w :
    0 <= x => 32*(x + 1) <= WArray.size =>
    get8 (set256 t x w) y = if 32*x <= y < 32*(x+1) then w \bits8 (y - 32*x) else get8 t y.
  proof.
    move=> hx hs; rewrite set256E /get8.
    case: (32 * x <= y < 32 * (x + 1)) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get_set256E t x y w:
    0 <= x => 32*(x + 1) <= WArray.size =>
    get256 (set256 t x w) y = if y = x then w else get256 t y.
  proof.
    move=> hx hs; rewrite set256E !get256E.
    case: (y = x) => [-> | hne].
    + rewrite -(W32u8.unpack8K w);congr.
      apply W32u8.Pack.ext_eq => k hk; rewrite W32u8.get_unpack8 //= W32u8.Pack.initiE //= initiE /#.
    congr; apply W32u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 32 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  hint simplify get_set8E, get8_set16E, get_set16E,
                           get8_set32E, get_set32E,
                           get8_set64E, get_set64E,
                           get8_set128E, get_set128E,
                           get8_set256E, get_set256E.

  (* ------------------------------------------------- *)

  op init8 (f:int -> W8.t) =
    init f.

  op init16 (f:int -> W16.t) =
    init (fun i => f (i %/ 2) \bits8 (i%%2)).

  op init32 (f:int -> W32.t) =
    init (fun i => f (i %/ 4) \bits8 (i%%4)).

  op init64 (f:int -> W64.t) =
    init (fun i => f (i %/ 8) \bits8 (i%%8)).

  op init128 (f:int -> W128.t) =
    init (fun i => f (i %/ 16) \bits8 (i%%16)).

  op init256 (f:int -> W256.t) =
    init (fun i => f (i %/ 32) \bits8 (i%%32)).

end WArray.



 
