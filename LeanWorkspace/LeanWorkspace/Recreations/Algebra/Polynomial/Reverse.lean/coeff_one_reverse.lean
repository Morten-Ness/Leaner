import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem coeff_one_reverse (f : R[X]) : coeff (Polynomial.reverse f) 1 = nextCoeff f := by
  rw [Polynomial.coeff_reverse, nextCoeff]
  split_ifs with hf
  · have : coeff f 1 = 0 := coeff_eq_zero_of_natDegree_lt (by simp only [hf, zero_lt_one])
    simp [*, Polynomial.revAt]
  · rw [Polynomial.revAt_le]
    exact Nat.succ_le_iff.2 (pos_iff_ne_zero.2 hf)

