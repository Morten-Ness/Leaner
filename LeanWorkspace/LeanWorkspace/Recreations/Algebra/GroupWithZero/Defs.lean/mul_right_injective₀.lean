import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective (a * ·) := fun _ _ => mul_left_cancel₀ ha

