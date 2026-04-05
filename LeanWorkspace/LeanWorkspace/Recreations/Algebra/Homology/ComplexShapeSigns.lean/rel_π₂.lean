import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂]

theorem rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) := TotalComplexShape.rel₂ i₁ h

