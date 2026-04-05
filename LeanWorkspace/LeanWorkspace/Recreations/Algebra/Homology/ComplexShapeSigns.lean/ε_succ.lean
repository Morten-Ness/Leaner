import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂]

variable {I : Type*} [AddMonoid I] (c : ComplexShape I)

variable [TensorSigns c]

theorem ε_succ {p q : I} (hpq : c.Rel p q) : c.ε q = - c.ε p := TensorSigns.ε'_succ p q hpq

