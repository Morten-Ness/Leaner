import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_const [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    f a = f 0 + b := by
  simpa using map_add_const f 0

