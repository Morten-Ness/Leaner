import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

variable [ExistsAddOfLE R]

theorem Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a := le_iff_le_iff_lt_iff_lt.2 hn.pow_neg_iff

