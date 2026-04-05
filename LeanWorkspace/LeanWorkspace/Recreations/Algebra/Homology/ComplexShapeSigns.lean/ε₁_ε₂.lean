import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂]

theorem ε₁_ε₂ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ =
      - ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ := Eq.trans (mul_one _).symm (by
    rw [← Int.units_mul_self (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂')), mul_assoc]
    conv_lhs =>
      arg 2
      rw [← mul_assoc, ComplexShape.ε₂_ε₁ c₁₂ h₁ h₂]
    rw [neg_mul, neg_mul, neg_mul, mul_neg, neg_inj, ← mul_assoc, ← mul_assoc,
      Int.units_mul_self, one_mul])

