import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n := by simp

