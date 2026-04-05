import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem mem_genWeightSpaceOf (χ : R) (x : L) (m : M) :
    m ∈ LieModule.genWeightSpaceOf M χ x ↔ ∃ k : ℕ, ((toEnd R L M x - χ • ↑1) ^ k) m = 0 := by
  simp [LieModule.genWeightSpaceOf]

