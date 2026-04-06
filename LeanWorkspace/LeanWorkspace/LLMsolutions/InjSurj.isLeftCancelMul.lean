import Mathlib

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]

theorem isLeftCancelMul [Mul M₂] [IsLeftCancelMul M₂] (f : M₁ → M₂) (hf : Function.Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsLeftCancelMul M₁ where
  mul_left_cancel x y z H := by
    apply hf
    have H' : f x * f y = f x * f z := by
      simpa [mul x y, mul x z] using congrArg f H
    exact IsLeftCancelMul.mul_left_cancel (a := f x) H'
