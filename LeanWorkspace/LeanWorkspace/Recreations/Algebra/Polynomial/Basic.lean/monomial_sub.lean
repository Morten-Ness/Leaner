import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem monomial_sub (n : ℕ) : Polynomial.monomial n (a - b) = Polynomial.monomial n a - Polynomial.monomial n b := by
  rw [sub_eq_add_neg, map_add, Polynomial.monomial_neg, sub_eq_add_neg]

