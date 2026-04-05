import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  simp [← coeff_natDegree, Polynomial.natDegree_mul' h, Polynomial.coeff_mul_degree_add_degree]

