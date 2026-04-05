import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a := by
  rw [Nat.lt_iff_add_one_le, zero_add, Nat.le_floor_iff' Nat.one_ne_zero, cast_one]

