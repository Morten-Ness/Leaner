import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem exists_genWeightSpace_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L → R) (x : L) :
    ∃ k : ℕ,
      LieModule.genWeightSpace M χ ≤ ((toEnd R L M x - algebraMap R _ (χ x)) ^ k).ker := by
  use (toEnd R L M x).maxGenEigenspaceIndex (χ x)
  intro m hm
  replace hm : m ∈ (toEnd R L M x).maxGenEigenspace (χ x) :=
    LieModule.genWeightSpace_le_genWeightSpaceOf M x χ hm
  rwa [Module.End.maxGenEigenspace_eq, Module.End.genEigenspace_nat] at hm

