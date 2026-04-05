import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

theorem IsMulTorsionFree.pow_right_injective {M : Type*} [CancelMonoid M] [IsMulTorsionFree M]
    {x : M} (hx : x ≠ 1) : Function.Injective (fun n ↦ x ^ n) := IsLeftRegular.pow_injective (IsLeftRegular.all x) hx

