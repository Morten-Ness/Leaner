import Mathlib

variable {R : Type*}

theorem pow_add_mul_le_add_pow [CommSemiring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R]
    {a b : R} (ha : 0 ≤ a) (H : 0 ≤ 2 * a + b) (n : ℕ) :
    a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n := (Commute.all a b).pow_add_mul_le_add_pow ha H n

