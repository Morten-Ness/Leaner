import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_trailingCoeff (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
    (Polynomial.trinomial k m n u v w).trailingCoeff = u := by
  rw [trailingCoeff, Polynomial.trinomial_natTrailingDegree hkm hmn hu, Polynomial.trinomial_trailing_coeff' hkm hmn]

