import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : ℕ}

theorem one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n := one_add_le_pow_of_two_add_nonneg (neg_le_iff_add_nonneg'.mp H) n

