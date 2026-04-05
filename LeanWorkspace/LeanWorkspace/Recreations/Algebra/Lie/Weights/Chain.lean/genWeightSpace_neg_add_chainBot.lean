import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

variable (hα : α ≠ 0)

theorem genWeightSpace_neg_add_chainBot :
    genWeightSpace M (-α + LieModule.chainBot α β : L → R) = ⊥ := by
  rw [← chainTop_neg, LieModule.genWeightSpace_add_chainTop _ _ (by simpa using hα)]

