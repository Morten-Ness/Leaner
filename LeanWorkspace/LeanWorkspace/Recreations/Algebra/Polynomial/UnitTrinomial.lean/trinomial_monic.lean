import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_monic (hkm : k < m) (hmn : m < n) : (Polynomial.trinomial k m n u v 1).Monic := by
  nontriviality R
  exact Polynomial.trinomial_leadingCoeff hkm hmn one_ne_zero

