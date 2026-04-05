import Mathlib

variable {R : Type*}

theorem eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  by_contra! h₁
  have h₂ : s₂ ≠ 0 := fun hc ↦ by simp_all
  rw [← isSumNonzeroSq_iff_isSumSq h₁] at hs₁
  rw [← isSumNonzeroSq_iff_isSumSq h₂] at hs₂
  exact not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.add hs₁ hs₂)

