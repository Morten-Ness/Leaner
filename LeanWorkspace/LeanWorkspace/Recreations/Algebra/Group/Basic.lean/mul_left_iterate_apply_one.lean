import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem mul_left_iterate_apply_one (a : M) : (a * ·)^[n] 1 = a ^ n := by simp

