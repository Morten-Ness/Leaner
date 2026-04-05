import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_Ioo {a b : R} (ha : 0 ≤ a) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  ext
  simp [Nat.floor_lt, lt_ceil, ha]

