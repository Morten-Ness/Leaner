FAIL
import Mathlib

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]

theorem isRightCancelMul [Mul M₂] [IsRightCancelMul M₂] (f : M₁ → M₂) (hf : Function.Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsRightCancelMul M₁ where
  mul_right_cancel := by
    intro a b c h
    apply hf
    have h' : f (a * c) = f (b * c) := congrArg f h
    rw [mul a c, mul b c] at h'
    exact IsRightCancelMul.mul_right_cancel (a := f a) (b := f b) (c := f c) h'
