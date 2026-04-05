import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem map_genWeightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (LieModule.genWeightSpace M χ).map e = LieModule.genWeightSpace M₂ χ := by
  simp [LieModule.map_genWeightSpace_eq_of_injective e.injective]

