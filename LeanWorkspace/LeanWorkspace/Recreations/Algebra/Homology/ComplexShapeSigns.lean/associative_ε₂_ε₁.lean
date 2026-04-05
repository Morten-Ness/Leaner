import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂]

variable [TotalComplexShape c₁₂ c₃ c] [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c]

variable [Associative c₁ c₂ c₃ c₁₂ c₂₃ c]

theorem associative_ε₂_ε₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₁ c₂ c₃ c₂₃ (i₂, i₃) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₂ c₁ c₂ c₁₂ (i₁, i₂) := by
  apply Associative.ε₂_ε₁

