import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeffs_one : Polynomial.coeffs (1 : R[X]) ⊆ {1} := by
  classical
  simp_rw [Polynomial.coeffs, Finset.image_subset_iff]
  simp_all [Polynomial.coeff_one]

