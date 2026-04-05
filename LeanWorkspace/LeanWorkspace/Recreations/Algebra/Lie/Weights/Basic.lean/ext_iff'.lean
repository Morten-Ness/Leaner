import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem ext_iff' {χ₁ χ₂ : LieModule.Weight R L M} : (χ₁ : L → R) = χ₂ ↔ χ₁ = χ₂ := by simp

