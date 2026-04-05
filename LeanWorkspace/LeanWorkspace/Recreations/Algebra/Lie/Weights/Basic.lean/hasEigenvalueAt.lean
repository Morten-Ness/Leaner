import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem hasEigenvalueAt (χ : LieModule.Weight R L M) (x : L) :
    (toEnd R L M x).HasEigenvalue (χ x) := by
  obtain ⟨k : ℕ, hk : (toEnd R L M x).genEigenspace (χ x) k ≠ ⊥⟩ := by
    simpa [LieModule.genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using χ.genWeightSpaceOf_ne_bot x
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue hk

