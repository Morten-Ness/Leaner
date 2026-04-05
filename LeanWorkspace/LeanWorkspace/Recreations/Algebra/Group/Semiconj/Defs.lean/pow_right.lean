import Mathlib

variable {S M G : Type*}

variable [Monoid M]

theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact SemiconjBy.one_right _
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact SemiconjBy.mul_right ih h

