import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natDegree_eraseLead (h : f.nextCoeff ≠ 0) : f.eraseLead.natDegree = f.natDegree - 1 := by
  have := natDegree_pos_of_nextCoeff_ne_zero h
  refine Polynomial.eraseLead_natDegree_le f.antisymm <| le_natDegree_of_ne_zero ?_
  rwa [Polynomial.eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne, ← nextCoeff_of_natDegree_pos]
  all_goals positivity

