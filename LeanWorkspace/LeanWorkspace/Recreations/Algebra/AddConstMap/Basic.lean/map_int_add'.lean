import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n • b := by
  rw [← AddConstMapClass.map_zsmul_add, zsmul_one]

