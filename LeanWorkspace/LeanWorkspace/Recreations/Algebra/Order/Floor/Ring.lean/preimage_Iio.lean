import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem preimage_Iio : ((↑) : ℤ → R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ := by
  ext
  simp [lt_ceil]

