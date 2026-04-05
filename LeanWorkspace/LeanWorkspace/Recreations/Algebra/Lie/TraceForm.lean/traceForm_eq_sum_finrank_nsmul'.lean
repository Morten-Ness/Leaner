import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

variable [LieRing.IsNilpotent L] [LinearWeights K L M] [IsTriangularizable K L M]

theorem traceForm_eq_sum_finrank_nsmul' :
    LieModule.traceForm K L M = ∑ χ ∈ {χ : Weight K L M | χ.IsNonZero}, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) := by
  classical
  suffices ∑ χ ∈ {χ : Weight K L M | χ.IsZero}, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) = 0 by
    rw [LieModule.traceForm_eq_sum_finrank_nsmul,
      ← Finset.sum_filter_add_sum_filter_not (p := fun χ : Weight K L M ↦ χ.IsNonZero)]
    simp [this]
  refine Finset.sum_eq_zero fun χ hχ ↦ ?_
  replace hχ : (χ : L →ₗ[K] K) = 0 := by simpa [← Weight.coe_toLinear_eq_zero_iff] using hχ
  simp [hχ]

-- The reverse inclusion should also hold: TODO prove this!

