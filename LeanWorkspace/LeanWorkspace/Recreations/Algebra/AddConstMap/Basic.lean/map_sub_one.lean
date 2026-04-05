import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x - 1) = f x - b := AddConstMapClass.map_sub_const f x

