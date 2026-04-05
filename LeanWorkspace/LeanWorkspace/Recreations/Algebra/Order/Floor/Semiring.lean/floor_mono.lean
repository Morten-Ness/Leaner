import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_mono : Monotone (floor : R → ℕ) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [Nat.floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((Nat.floor_le ha).trans h)

