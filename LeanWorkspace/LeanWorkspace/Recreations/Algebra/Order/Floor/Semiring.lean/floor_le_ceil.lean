import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_le_ceil (a : R) : ⌊a⌋₊ ≤ ⌈a⌉₊ := by
  obtain ha | ha := le_total a 0
  · rw [Nat.floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact cast_le.1 ((Nat.floor_le ha).trans <| Nat.le_ceil _)

