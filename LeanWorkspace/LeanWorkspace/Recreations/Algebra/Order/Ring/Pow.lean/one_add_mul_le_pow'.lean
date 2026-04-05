import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b : R}

theorem one_add_mul_le_pow' (Hsq : 0 ≤ a * a) (Hsq' : 0 ≤ (1 + a) * (1 + a)) (H : 0 ≤ 2 + a) (n : ℕ) :
    1 + n * a ≤ (1 + a) ^ n := one_add_mul_le_pow_of_sq_nonneg (by rwa [sq]) (by rwa [sq]) H n

