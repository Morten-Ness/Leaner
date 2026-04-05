import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] [IsDomain R]

theorem traceForm_eq_sum_genWeightSpaceOf [IsPrincipalIdealRing R]
    [Module.IsTorsionFree R M] [IsNoetherian R M] [IsTriangularizable R L M] (z : L) :
    LieModule.traceForm R L M =
    ∑ χ ∈ (finite_genWeightSpaceOf_ne_bot R L M z).toFinset,
      LieModule.traceForm R L (genWeightSpaceOf M χ z) := by
  ext x y
  have hxy : ∀ χ : R, MapsTo ((toEnd R L M x).comp (toEnd R L M y))
      (genWeightSpaceOf M χ z) (genWeightSpaceOf M χ z) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (genWeightSpaceOf M χ z : Submodule R M) ≠ ⊥}.Finite := by
    simp_rw [ne_eq, LieSubmodule.toSubmodule_eq_bot (genWeightSpaceOf M _ _)]
    exact finite_genWeightSpaceOf_ne_bot R L M z
  classical
  have h := LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpaceOf R L M z
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h <| by
    simp [← LieSubmodule.iSup_toSubmodule]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LieModule.traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ ↦ rfl)

-- In characteristic zero (or even just `LinearWeights R L M`) a stronger result holds (no
-- `⊓ LieAlgebra.center R L`) TODO prove this using `LieModule.traceForm_eq_sum_finrank_nsmul_mul`.

