import Mathlib

variable {R : Type*}

theorem eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₂ = 0 := by
  simp_all [IsFormallyReal.eq_zero_of_add_right hs₁ hs₂ h]

