import Mathlib

variable {M₀ G₀ M₀' G₀' : Type*}

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

theorem Function.Injective.noZeroDivisors [NoZeroDivisors M₀'] : NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} H := have : f a * f b = 0 := by rw [← mul, H, zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
      (fun H ↦ hf <| by rwa [zero]) fun H ↦ hf <| by rwa [zero]

