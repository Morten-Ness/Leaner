import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  simpa using AddConstMapClass.map_sub_nsmul f x 1

