import Mathlib

variable {α M R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b x y : R} {n : ℕ}

theorem pow_add_pow_le' (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ n + b ^ n ≤ 2 * (a + b) ^ n := by
  rw [two_mul]
  gcongr <;> try assumption
  exacts [le_add_of_nonneg_right hb, le_add_of_nonneg_left ha]

