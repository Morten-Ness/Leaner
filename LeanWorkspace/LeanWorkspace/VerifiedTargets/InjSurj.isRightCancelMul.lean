import Mathlib

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]

theorem isRightCancelMul [Mul M₂] [IsRightCancelMul M₂] (f : M₁ → M₂) (hf : Function.Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsRightCancelMul M₁ where
  mul_right_cancel x y z H := hf <| mul_right_cancel <| by simpa only [mul] using congrArg f H

