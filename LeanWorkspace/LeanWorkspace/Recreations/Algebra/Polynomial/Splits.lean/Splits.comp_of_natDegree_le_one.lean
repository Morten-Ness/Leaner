import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.comp_of_natDegree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.natDegree ≤ 1) :
    (f.comp g).Splits := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  · exact Polynomial.Splits.comp_of_natDegree_le_one_of_invertible hf hg
      (invertibleOfNonzero (leadingCoeff_ne_zero.mpr hg0))

