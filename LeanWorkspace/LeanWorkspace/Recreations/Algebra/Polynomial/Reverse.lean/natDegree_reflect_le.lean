import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natDegree_reflect_le {N : ℕ} {p : R[X]} :
    (p.reflect N).natDegree ≤ max N p.natDegree := by
  simp +contextual [-le_sup_iff, natDegree_le_iff_coeff_eq_zero,
    Polynomial.revAt, not_le_of_gt, coeff_eq_zero_of_natDegree_lt]

