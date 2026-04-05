import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natDegree_eq_reverse_natDegree_add_natTrailingDegree (f : R[X]) :
    f.natDegree = f.reverse.natDegree + f.natTrailingDegree := by
  by_cases hf : f = 0
  · rw [hf, Polynomial.reverse_zero, natDegree_zero, natTrailingDegree_zero]
  apply le_antisymm
  · refine tsub_le_iff_right.mp ?_
    apply le_natDegree_of_ne_zero
    rw [Polynomial.reverse, Polynomial.coeff_reflect, ← Polynomial.revAt_le f.natTrailingDegree_le_natDegree, Polynomial.revAt_invol]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hf
  · rw [← le_tsub_iff_left Polynomial.reverse_natDegree_le f]
    apply natTrailingDegree_le_of_ne_zero
    have key := mt leadingCoeff_eq_zero.mp (mt Polynomial.reverse_eq_zero.mp hf)
    rwa [leadingCoeff, Polynomial.coeff_reverse, Polynomial.revAt_le Polynomial.reverse_natDegree_le f] at key

