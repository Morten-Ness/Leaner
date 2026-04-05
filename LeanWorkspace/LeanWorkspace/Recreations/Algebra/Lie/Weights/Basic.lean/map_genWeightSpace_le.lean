import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem map_genWeightSpace_le :
    (LieModule.genWeightSpace M χ).map f ≤ LieModule.genWeightSpace M₂ χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  simp only [LieSubmodule.mem_comap, LieModule.mem_genWeightSpace]
  intro x
  have : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f = f ∘ₗ (toEnd R L M x - χ x • ↑1) := by
    ext; simp
  obtain ⟨k, h⟩ := (LieModule.mem_genWeightSpace _ _ _).mp hm x
  refine ⟨k, ?_⟩
  simpa [h] using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute this k) m

