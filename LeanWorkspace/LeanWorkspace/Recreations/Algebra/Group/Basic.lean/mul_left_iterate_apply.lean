import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem mul_left_iterate_apply (a b : M) : (a * ·)^[n] b = a ^ n * b := by simp

