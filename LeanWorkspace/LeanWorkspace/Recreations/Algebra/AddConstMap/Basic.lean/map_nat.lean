import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) : f n = f 0 + n := by simp

