import Mathlib

variable {S M G : Type*}

variable [Monoid M]

theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  simpa using h.pow_right n
