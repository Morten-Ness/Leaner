import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

variable (hα : α ≠ 0)

theorem genWeightSpace_chainTopCoeff_add_one_nsmul_add :
    genWeightSpace M ((LieModule.chainTopCoeff α β + 1) • α + β : L → R) = ⊥ := by
  classical
  rw [LieModule.chainTopCoeff_add_one _ _ hα]
  exact Nat.find_spec (LieModule.eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists

