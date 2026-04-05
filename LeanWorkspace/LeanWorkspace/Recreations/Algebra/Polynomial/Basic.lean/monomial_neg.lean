import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem monomial_neg (n : ℕ) (a : R) : Polynomial.monomial n (-a) = -Polynomial.monomial n a := by
  rw [eq_neg_iff_add_eq_zero, ← map_add, neg_add_cancel, Polynomial.monomial_zero_right]

