import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n := by simp

