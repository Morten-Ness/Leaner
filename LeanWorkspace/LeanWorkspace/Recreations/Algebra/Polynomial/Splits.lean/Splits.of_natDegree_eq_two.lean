import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.of_natDegree_eq_two {x : R} (h₁ : f.natDegree = 2) (h₂ : f.eval x = 0) :
    Polynomial.Splits f := by
  have h : (f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C x), h₁, natDegree_X_sub_C]
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂, Polynomial.splits_mul_iff (X_sub_C_ne_zero x) (by aesop)]
  exact ⟨Polynomial.Splits.X_sub_C x, Polynomial.Splits.of_natDegree_eq_one h⟩

