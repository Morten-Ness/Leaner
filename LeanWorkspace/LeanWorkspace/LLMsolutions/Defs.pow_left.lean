import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b := by
  simpa using h.pow_left n
