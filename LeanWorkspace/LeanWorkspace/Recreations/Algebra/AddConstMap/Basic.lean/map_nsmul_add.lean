import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, AddConstMapClass.map_add_nsmul]

