import Mathlib

variable {R : Type*}

theorem one_add_le_pow_of_two_add_nonneg [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a : R} (H : 0 ≤ 2 + a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n := one_add_mul_le_pow_of_sq_nonneg (sq_nonneg _) (sq_nonneg _) H _

