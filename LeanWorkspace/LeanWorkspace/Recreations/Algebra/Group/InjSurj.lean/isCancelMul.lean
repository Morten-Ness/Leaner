import Mathlib

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]

theorem isCancelMul [Mul M₂] [IsCancelMul M₂] (f : M₁ → M₂) (hf : Function.Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsCancelMul M₁ where
  __ := Function.Injective.isLeftCancelMul hf f mul
  __ := Function.Injective.isRightCancelMul hf f mul

