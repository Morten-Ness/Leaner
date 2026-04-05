import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem mul_right_iterate (a : M) : ∀ n : ℕ, (· * a)^[n] = (· * a ^ n)
  | 0 => by ext; simp
  | n + 1 => by simp [pow_succ', mul_right_iterate]
