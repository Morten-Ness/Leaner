import Mathlib

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

variable [TotalComplexShape c₁ c₂ c₁₂]

variable {I : Type*} [AddMonoid I] (c : ComplexShape I)

variable [TensorSigns c]

theorem next_add' (p q : I) (hq : c.Rel q (c.next q)) :
    c.next (p + q) = p + c.next q := c.next_eq' (ComplexShape.add_rel c p hq)

