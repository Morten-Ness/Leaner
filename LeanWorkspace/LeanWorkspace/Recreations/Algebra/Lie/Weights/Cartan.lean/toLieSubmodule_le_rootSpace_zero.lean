import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem toLieSubmodule_le_rootSpace_zero : H.toLieSubmodule ≤ rootSpace H 0 := by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_genWeightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R H H
  use k
  let f : Module.End R H := toEnd R H H y
  let g : Module.End R L := toEnd R H L y
  have hfg : g.comp (H : Submodule R L).subtype = (H : Submodule R L).subtype.comp f := rfl
  change (g ^ k).comp (H : Submodule R L).subtype ⟨x, hx⟩ = 0
  rw [Module.End.commute_pow_left_of_commute hfg k]
  have h := iterate_toEnd_mem_lowerCentralSeries R H H y ⟨x, hx⟩ k
  rw [hk, LieSubmodule.mem_bot] at h
  simp only [Submodule.subtype_apply, Function.comp_apply, Module.End.pow_apply, LinearMap.coe_comp,
    Submodule.coe_eq_zero]
  exact h

