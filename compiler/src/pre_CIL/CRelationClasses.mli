
type __ = Obj.t

type 'a crelation = __

type ('a, 'b) arrow = 'a -> 'b

type ('a, 'b) iffT = ('a -> 'b) * ('b -> 'a)

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x
