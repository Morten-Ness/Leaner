import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_Ioc {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  ext
  simp [Nat.floor_lt, le_floor_iff, hb, ha]

