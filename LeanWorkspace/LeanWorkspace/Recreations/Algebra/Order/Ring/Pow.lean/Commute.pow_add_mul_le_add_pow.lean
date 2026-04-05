import Mathlib

variable {R : Type*}

theorem Commute.pow_add_mul_le_add_pow [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a b : R} (Hcomm : Commute a b) (ha : 0 ≤ a) (H : 0 ≤ 2 * a + b)
    (n : ℕ) : a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n := Hcomm.pow_add_mul_le_add_pow_of_sq_nonneg ha (sq_nonneg _) (sq_nonneg _) H n

