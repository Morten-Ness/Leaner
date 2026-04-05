import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem leadingCoeff_eraseLead_eq_nextCoeff (h : f.nextCoeff ≠ 0) :
    f.eraseLead.leadingCoeff = f.nextCoeff := by
  have := natDegree_pos_of_nextCoeff_ne_zero h
  rw [leadingCoeff, nextCoeff, Polynomial.natDegree_eraseLead h, if_neg,
    Polynomial.eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne]
  all_goals positivity

