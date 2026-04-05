import Mathlib

variable {R : Type*}

theorem pow_add_mul_le_add_pow_of_sq_nonneg [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {a b : R} (ha : 0 ≤ a) (Hsq : 0 ≤ b ^ 2) (Hsq' : 0 ≤ (a + b) ^ 2) (H : 0 ≤ 2 * a + b)
    (n : ℕ) : a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n := (Commute.all a b).pow_add_mul_le_add_pow_of_sq_nonneg ha Hsq Hsq' H n

