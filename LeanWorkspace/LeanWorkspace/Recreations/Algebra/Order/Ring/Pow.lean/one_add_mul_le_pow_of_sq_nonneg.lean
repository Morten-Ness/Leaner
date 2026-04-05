import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b : R}

theorem one_add_mul_le_pow_of_sq_nonneg (Hsq : 0 ≤ a ^ 2) (Hsq' : 0 ≤ (1 + a) ^ 2) (H : 0 ≤ 2 + a)
    (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n := by
  simpa using (Commute.one_left a).pow_add_mul_le_add_pow_of_sq_nonneg zero_le_one Hsq Hsq'
    (by simpa using H) n

