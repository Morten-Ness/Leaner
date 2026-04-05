import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem preimage_Ico {a b : R} : ((↑) : ℤ → R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉ := by
  ext
  simp [ceil_le, lt_ceil]

