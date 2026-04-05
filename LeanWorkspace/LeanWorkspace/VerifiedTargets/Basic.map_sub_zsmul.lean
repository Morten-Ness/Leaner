import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℤ) : f (x - n • a) = f x - n • b := by
  simpa [sub_eq_add_neg] using AddConstMapClass.map_add_zsmul f x (-n)

