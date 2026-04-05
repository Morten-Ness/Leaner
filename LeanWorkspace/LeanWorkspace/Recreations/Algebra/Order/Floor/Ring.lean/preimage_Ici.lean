import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem preimage_Ici : ((↑) : ℤ → R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ := by
  ext
  simp [ceil_le]

