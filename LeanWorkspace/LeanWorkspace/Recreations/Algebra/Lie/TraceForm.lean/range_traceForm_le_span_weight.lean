import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

variable [LieRing.IsNilpotent L] [LinearWeights K L M] [IsTriangularizable K L M]

theorem range_traceForm_le_span_weight :
    LinearMap.range (LieModule.traceForm K L M) ≤ span K (Set.range (Weight.toLinear K L M)) := by
  rintro - ⟨x, rfl⟩
  rw [LieModule.traceForm_eq_sum_finrank_nsmul, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun χ _ ↦ ?_
  simp_rw [LinearMap.smul_apply, LinearMap.coe_smulRight, Weight.toLinear_apply,
    ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem _ _ <| Submodule.smul_mem _ _ <| subset_span <| mem_range_self χ

