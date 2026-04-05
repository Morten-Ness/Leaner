import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_one_add [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (1 + x) = f x + b := AddConstMapClass.map_const_add f x

