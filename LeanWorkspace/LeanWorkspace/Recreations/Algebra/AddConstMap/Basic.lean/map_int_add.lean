import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n := by simp

