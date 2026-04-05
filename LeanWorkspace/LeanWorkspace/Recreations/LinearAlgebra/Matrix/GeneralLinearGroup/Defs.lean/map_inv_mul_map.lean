import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable {S T : Type*} [CommRing S] [CommRing T]

variable (f : R →+* S)

theorem map_inv_mul_map (g : GL n R) : Matrix.GeneralLinearGroup.map f g⁻¹ * Matrix.GeneralLinearGroup.map f g = 1 := by
  simp only [map_inv, inv_mul_cancel]

