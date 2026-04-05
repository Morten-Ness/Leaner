import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂]

theorem prev_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ := c₁₂.prev_eq' (ComplexShape.rel_π₂ c₁ c₁₂ i₁ h)

