import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

variable [LieRing.IsNilpotent L] [LinearWeights K L M] [IsTriangularizable K L M]

theorem traceForm_eq_sum_finrank_nsmul :
    LieModule.traceForm K L M = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) := by
  ext
  rw [LieModule.traceForm_eq_sum_finrank_nsmul_mul, ← Finset.sum_attach]
  simp [-LinearMap.coe_smul]

