import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem map_genWeightSpace_eq_of_injective (hf : Function.Injective f) :
    (LieModule.genWeightSpace M χ).map f = LieModule.genWeightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm (le_inf_iff.mpr ⟨LieModule.map_genWeightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← LieModule.comap_genWeightSpace_eq_of_injective hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩

