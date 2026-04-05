import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem comap_genWeightSpace_eq_of_injective (hf : Function.Injective f) :
    (LieModule.genWeightSpace M₂ χ).comap f = LieModule.genWeightSpace M χ := by
  refine le_antisymm (fun m hm ↦ ?_) ?_
  · simp only [LieSubmodule.mem_comap, LieModule.mem_genWeightSpace] at hm
    simp only [LieModule.mem_genWeightSpace]
    intro x
    have h : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f =
             f ∘ₗ (toEnd R L M x - χ x • ↑1) := by ext; simp
    obtain ⟨k, hk⟩ := hm x
    use k
    suffices f (((toEnd R L M x - χ x • ↑1) ^ k) m) = 0 by
      rw [← map_zero f] at this; exact hf this
    simpa [hk] using (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h k) m).symm
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact LieModule.map_genWeightSpace_le f

