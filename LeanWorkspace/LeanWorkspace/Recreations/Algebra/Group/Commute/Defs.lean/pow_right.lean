import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) := SemiconjBy.pow_right h n

