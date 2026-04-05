import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, AddConstMapClass.map_add_zsmul]

