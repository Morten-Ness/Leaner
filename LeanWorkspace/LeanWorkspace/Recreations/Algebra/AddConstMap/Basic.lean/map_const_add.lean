import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_const_add [AddCommMagma G] [Add H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (a + x) = f x + b := by
  rw [add_comm, map_add_const]

