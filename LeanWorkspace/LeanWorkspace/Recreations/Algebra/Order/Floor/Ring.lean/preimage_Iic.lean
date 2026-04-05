import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem preimage_Iic : ((↑) : ℤ → R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ := by
  ext
  simp [le_floor]

