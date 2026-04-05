import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_Icc {a b : R} (hb : 0 ≤ b) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  ext
  simp [ceil_le, hb, le_floor_iff]

