import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

variable [ExistsAddOfLE R]

theorem Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n := (hn.pow_nonneg _).lt_of_ne' (pow_ne_zero _ ha)

