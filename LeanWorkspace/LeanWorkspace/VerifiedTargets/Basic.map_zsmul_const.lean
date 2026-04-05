import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) : f (n • a) = f 0 + n • b := by
  simpa using AddConstMapClass.map_add_zsmul f 0 n

