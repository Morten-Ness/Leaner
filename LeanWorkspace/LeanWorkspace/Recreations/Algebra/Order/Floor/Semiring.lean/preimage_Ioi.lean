import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_Ioi {a : R} (ha : 0 ≤ a) : (Nat.cast : ℕ → R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊ := by
  ext
  simp [Nat.floor_lt, ha]

