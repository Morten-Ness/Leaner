import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_Iic {a : R} (ha : 0 ≤ a) : (Nat.cast : ℕ → R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊ := by
  ext
  simp [le_floor_iff, ha]

