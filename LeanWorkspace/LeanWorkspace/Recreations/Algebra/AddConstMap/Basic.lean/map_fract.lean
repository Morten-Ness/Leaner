import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_fract {R : Type*} [Ring R] [LinearOrder R] [FloorRing R] [AddGroup H]
    [FunLike F R H] [AddConstMapClass F R H 1 b] (f : F) (x : R) :
    f (Int.fract x) = f x - ⌊x⌋ • b := AddConstMapClass.map_sub_int' ..

