import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem mul_right_iterate_apply_one (a : M) : (· * a)^[n] 1 = a ^ n := by simp [mul_right_iterate]

