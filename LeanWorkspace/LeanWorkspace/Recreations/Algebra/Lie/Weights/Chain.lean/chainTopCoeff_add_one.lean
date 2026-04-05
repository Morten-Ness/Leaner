import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

variable (hα : α ≠ 0)

theorem chainTopCoeff_add_one :
    letI := Classical.propDecidable
    LieModule.chainTopCoeff α β + 1 =
      Nat.find (LieModule.eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists := by
  classical
  rw [LieModule.chainTopCoeff, dif_neg hα]
  apply Nat.succ_pred_eq_of_pos
  rw [zero_lt_iff]
  intro e
  have : genWeightSpace M (0 • α + β : L → R) = ⊥ := by
    rw [← e]
    exact Nat.find_spec (LieModule.eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists
  exact β.genWeightSpace_ne_bot _ (by simpa only [zero_smul, zero_add] using this)

