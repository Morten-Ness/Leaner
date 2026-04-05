import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c := IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h

