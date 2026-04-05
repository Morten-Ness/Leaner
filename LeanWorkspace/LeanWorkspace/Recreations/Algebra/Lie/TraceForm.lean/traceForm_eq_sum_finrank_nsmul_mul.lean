import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

variable [LieRing.IsNilpotent L] [LinearWeights K L M] [IsTriangularizable K L M]

set_option backward.isDefEq.respectTransparency false in
theorem traceForm_eq_sum_finrank_nsmul_mul (x y : L) :
    LieModule.traceForm K L M x y = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ x * χ y) := by
  have hxy : ∀ χ : Weight K L M, MapsTo (toEnd K L M x ∘ₗ toEnd K L M y)
      (genWeightSpace M χ) (genWeightSpace M χ) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace' K L M)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top' K L M)
  simp_rw [LieModule.traceForm_apply_apply, LinearMap.trace_eq_sum_trace_restrict hds hxy,
    ← LieModule.traceForm_genWeightSpace_eq K L M _ x y]
  rfl

