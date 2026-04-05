import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

variable (hα : α ≠ 0)

theorem genWeightSpace_chainBotCoeff_sub_one_zsmul_sub :
    genWeightSpace M ((-LieModule.chainBotCoeff α β - 1 : ℤ) • α + β : L → R) = ⊥ := by
  rw [sub_eq_add_neg, ← neg_add, neg_smul, ← smul_neg, LieModule.chainBotCoeff,
    LieModule.genWeightSpace_chainTopCoeff_add_one_zsmul_add _ _ (by simpa using hα)]

