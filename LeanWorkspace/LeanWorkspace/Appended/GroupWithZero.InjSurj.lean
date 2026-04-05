import Mathlib

section

variable {M₀ G₀ M₀' G₀' : Type*}

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

theorem Function.Injective.isCancelMulZero
    [IsCancelMulZero M₀'] : IsCancelMulZero M₀ where
  __ := hf.isLeftCancelMulZero f zero mul
  __ := hf.isRightCancelMulZero f zero mul

end

section

variable {M₀ G₀ M₀' G₀' : Type*}

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

theorem Function.Injective.isLeftCancelMulZero
    [IsLeftCancelMulZero M₀'] : IsLeftCancelMulZero M₀ where
  mul_left_cancel_of_ne_zero Hne _ _ He := by
    have := congr_arg f He
    rw [mul, mul] at this
    exact hf (mul_left_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)

end

section

variable {M₀ G₀ M₀' G₀' : Type*}

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

theorem Function.Injective.isRightCancelMulZero
    [IsRightCancelMulZero M₀'] : IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero Hne _ _ He := by
    have := congr_arg f He
    rw [mul, mul] at this
    exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)

end

section

variable {M₀ G₀ M₀' G₀' : Type*}

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

theorem Function.Injective.noZeroDivisors [NoZeroDivisors M₀'] : NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} H := have : f a * f b = 0 := by rw [← mul, H, zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
      (fun H ↦ hf <| by rwa [zero]) fun H ↦ hf <| by rwa [zero]

end
