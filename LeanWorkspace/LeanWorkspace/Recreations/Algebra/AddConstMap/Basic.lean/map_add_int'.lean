import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n • b := by
  rw [← AddConstMapClass.map_add_zsmul f x n, zsmul_one]

