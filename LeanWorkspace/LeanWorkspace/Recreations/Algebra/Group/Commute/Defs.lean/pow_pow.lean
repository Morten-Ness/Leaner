import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) := by
  simp [h]

