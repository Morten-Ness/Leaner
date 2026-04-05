import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_leadingCoeff (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
    (Polynomial.trinomial k m n u v w).leadingCoeff = w := by
  rw [leadingCoeff, Polynomial.trinomial_natDegree hkm hmn hw, Polynomial.trinomial_leading_coeff' hkm hmn]

