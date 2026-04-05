import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n := lt_iff_lt_of_le_iff_le <| le_floor_iff ha

