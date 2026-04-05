import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

theorem IsMulTorsionFree.pow_right_inj {M : Type*} [CancelMonoid M] [IsMulTorsionFree M] {x : M}
    (hx : x ≠ 1) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := (pow_right_injective hx).eq_iff

