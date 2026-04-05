import Mathlib

variable {M₀ G₀ M₀' G₀' : Type*}

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

theorem Function.Injective.isRightCancelMulZero
    [IsRightCancelMulZero M₀'] : IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero Hne _ _ He := by
    have := congr_arg f He
    rw [mul, mul] at this
    exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)

