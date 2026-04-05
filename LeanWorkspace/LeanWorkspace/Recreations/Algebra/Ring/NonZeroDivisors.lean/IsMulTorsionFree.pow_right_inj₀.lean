import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

theorem IsMulTorsionFree.pow_right_inj₀ {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
    [IsMulTorsionFree M] {x : M} (hx : x ≠ 1) (hx' : x ≠ 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := (pow_right_injective₀ hx hx').eq_iff

