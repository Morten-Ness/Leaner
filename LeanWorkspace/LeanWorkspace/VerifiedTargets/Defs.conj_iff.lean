import Mathlib

variable {S M G : Type*}

variable [Group G]

theorem conj_iff {a x y b : G} :
    SemiconjBy (b * a * b⁻¹) (b * x * b⁻¹) (b * y * b⁻¹) ↔ SemiconjBy a x y := by
  unfold SemiconjBy
  simp only [← mul_assoc, inv_mul_cancel_right]
  repeat rw [mul_assoc]
  rw [mul_left_cancel_iff, ← mul_assoc, ← mul_assoc, mul_right_cancel_iff]

