import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

theorem IsMulTorsionFree.pow_right_injective₀ {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
    [IsMulTorsionFree M] {x : M} (hx : x ≠ 1) (hx' : x ≠ 0) : Function.Injective (fun n ↦ x ^ n) := IsLeftRegular.pow_injective (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx') hx

