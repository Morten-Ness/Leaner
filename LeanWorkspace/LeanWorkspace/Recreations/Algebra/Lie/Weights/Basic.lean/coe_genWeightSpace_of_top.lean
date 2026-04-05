import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem coe_genWeightSpace_of_top (χ : L → R) :
    (LieModule.genWeightSpace M (χ ∘ (⊤ : LieSubalgebra R L).incl) : Submodule R M) = LieModule.genWeightSpace M χ := by
  ext m
  simp only [LieModule.mem_genWeightSpace, LieSubmodule.mem_toSubmodule, Subtype.forall]
  apply forall_congr'
  simp

