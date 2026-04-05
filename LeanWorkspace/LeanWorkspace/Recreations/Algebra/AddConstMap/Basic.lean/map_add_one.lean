import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_one [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x + 1) = f x + b := map_add_const f x

