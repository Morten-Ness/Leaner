import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_lt_ceil_of_lt_of_pos {a b : R} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ := by
  rcases le_or_gt 0 a with (ha | ha)
  · rw [Nat.floor_lt ha]
    exact h.trans_le (Nat.le_ceil _)
  · rwa [Nat.floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]

