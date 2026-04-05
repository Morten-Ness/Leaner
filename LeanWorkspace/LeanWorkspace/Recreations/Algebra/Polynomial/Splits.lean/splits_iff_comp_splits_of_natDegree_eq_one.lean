import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem splits_iff_comp_splits_of_natDegree_eq_one {f g : R[X]} (hg : g.natDegree = 1) :
    f.Splits ↔ (f.comp g).Splits := by
  refine ⟨fun hf ↦ hf.comp_of_natDegree_le_one hg.le, fun hf ↦ ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hg.le
  have ha : a ≠ 0 := by contrapose! hg; simp [hg]
  have : f = (f.comp (C a * X + C b)).comp ((C a⁻¹ * (X - C b))) := by
    simp only [comp_assoc, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, sub_add_cancel, comp_X]
  rw [this]
  refine Polynomial.Splits.comp_of_natDegree_le_one hf ?_
  rw [natDegree_C_mul (mt inv_eq_zero.mp ha), natDegree_X_sub_C]

