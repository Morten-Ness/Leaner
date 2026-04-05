import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

theorem genWeightSpace_nsmul_add_ne_bot_of_le {n} (hn : n ≤ LieModule.chainTopCoeff α β) :
    genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by
  by_cases hα : α = 0
  · rw [hα, smul_zero, zero_add]; exact β.genWeightSpace_ne_bot
  classical
  rw [← Nat.lt_succ_iff, Nat.succ_eq_add_one, LieModule.chainTopCoeff_add_one _ _ hα] at hn
  exact Nat.find_min (LieModule.eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists hn

