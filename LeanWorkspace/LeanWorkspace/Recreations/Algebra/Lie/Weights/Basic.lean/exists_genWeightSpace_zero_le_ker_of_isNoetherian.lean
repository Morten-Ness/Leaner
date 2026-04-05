import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem exists_genWeightSpace_zero_le_ker_of_isNoetherian
    [IsNoetherian R M] (x : L) :
    ∃ k : ℕ, LieModule.genWeightSpace M (0 : L → R) ≤ LinearMap.ker (toEnd R L M x ^ k) := by
  simpa using LieModule.exists_genWeightSpace_le_ker_of_isNoetherian M (0 : L → R) x

