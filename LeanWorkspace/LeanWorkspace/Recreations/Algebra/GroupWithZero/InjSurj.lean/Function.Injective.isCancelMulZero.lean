import Mathlib

variable {M₀ G₀ M₀' G₀' : Type*}

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

theorem Function.Injective.isCancelMulZero
    [IsCancelMulZero M₀'] : IsCancelMulZero M₀ where
  __ := hf.isLeftCancelMulZero f zero mul
  __ := hf.isRightCancelMulZero f zero mul

