import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_one [AddZeroClass G] [One G] [Add H] [AddConstMapClass F G H 1 b] (f : F) :
    f 1 = f 0 + b := AddConstMapClass.map_const f

