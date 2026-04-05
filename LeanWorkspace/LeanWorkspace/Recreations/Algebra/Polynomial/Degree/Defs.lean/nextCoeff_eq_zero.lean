import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

theorem nextCoeff_eq_zero :
    p.nextCoeff = 0 ↔ p.natDegree = 0 ∨ 0 < p.natDegree ∧ p.coeff (p.natDegree - 1) = 0 := by
  simp [Polynomial.nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; simp_all

