import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b := fun _ _ => mul_right_cancel₀ hb

