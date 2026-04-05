import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : R) ≤ a := (le_floor_iff ha).1 le_rfl

