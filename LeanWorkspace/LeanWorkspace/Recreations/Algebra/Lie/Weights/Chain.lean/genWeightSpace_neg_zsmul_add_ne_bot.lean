import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

theorem genWeightSpace_neg_zsmul_add_ne_bot {n : ℕ} (hn : n ≤ LieModule.chainBotCoeff α β) :
    genWeightSpace M ((-n : ℤ) • α + β : L → R) ≠ ⊥ := by
  apply LieModule.genWeightSpace_zsmul_add_ne_bot α β <;> lia

