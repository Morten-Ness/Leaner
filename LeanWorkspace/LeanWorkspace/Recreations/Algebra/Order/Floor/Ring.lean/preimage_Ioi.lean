import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem preimage_Ioi : ((↑) : ℤ → R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ := by
  ext
  simp [floor_lt]

