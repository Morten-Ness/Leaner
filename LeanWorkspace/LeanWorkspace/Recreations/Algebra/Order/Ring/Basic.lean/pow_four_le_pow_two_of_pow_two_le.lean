import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R] {m n : ℕ}

theorem pow_four_le_pow_two_of_pow_two_le {a b : R} (h : a ^ 2 ≤ b) : a ^ 4 ≤ b ^ 2 := (pow_mul a 2 2).symm ▸ pow_le_pow_left₀ (sq_nonneg a) h 2

