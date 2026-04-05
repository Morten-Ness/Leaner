import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

theorem preimage_Iio {a : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊ := by
  ext
  simp [lt_ceil]

