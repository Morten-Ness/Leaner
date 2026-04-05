import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetry c₁ c₂ c₁₂]

theorem π_symm (i₁ : I₁) (i₂ : I₂) :
    π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ := by
  apply TotalComplexShapeSymmetry.symm

