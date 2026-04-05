import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

theorem eq_zero_or_one_of_sq_eq_self [MonoidWithZero M₀] [IsRightCancelMulZero M₀]
    {x : M₀} (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 := or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

