import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable {S T : Type*} [CommRing S] [CommRing T]

variable (f : R →+* S)

theorem map_mul_map_inv (g : GL n R) : Matrix.GeneralLinearGroup.map f g * Matrix.GeneralLinearGroup.map f g⁻¹ = 1 := by
  simp only [map_inv, mul_inv_cancel]

