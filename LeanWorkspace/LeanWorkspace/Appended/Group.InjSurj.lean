import Mathlib

section

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]

theorem isLeftCancelMul [Mul M₂] [IsLeftCancelMul M₂] (f : M₁ → M₂) (hf : Function.Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsLeftCancelMul M₁ where
  mul_left_cancel x y z H := hf <| mul_left_cancel <| by simpa only [mul] using congrArg f H

end

section

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]

theorem isRightCancelMul [Mul M₂] [IsRightCancelMul M₂] (f : M₁ → M₂) (hf : Function.Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsRightCancelMul M₁ where
  mul_right_cancel x y z H := hf <| mul_right_cancel <| by simpa only [mul] using congrArg f H

end
