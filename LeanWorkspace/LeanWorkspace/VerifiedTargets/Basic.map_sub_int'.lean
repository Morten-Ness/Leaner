import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n • b := by
  rw [← AddConstMapClass.map_sub_zsmul, zsmul_one]

