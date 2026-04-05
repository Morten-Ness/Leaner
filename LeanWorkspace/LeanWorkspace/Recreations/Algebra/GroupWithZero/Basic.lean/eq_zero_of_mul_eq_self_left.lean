import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem eq_zero_of_mul_eq_self_left [IsRightCancelMulZero M₀] (h₁ : b ≠ 1) (h₂ : b * a = a) :
    a = 0 := Classical.byContradiction fun ha => h₁ <| mul_right_cancel₀ ha <| h₂.symm ▸ (one_mul a).symm

