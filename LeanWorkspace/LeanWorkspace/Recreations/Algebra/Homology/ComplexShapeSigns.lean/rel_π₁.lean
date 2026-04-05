import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂]

theorem rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) := TotalComplexShape.rel₁ h i₂

