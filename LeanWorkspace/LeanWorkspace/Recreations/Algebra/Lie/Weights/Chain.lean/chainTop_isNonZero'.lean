import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

variable (hα : α ≠ 0)

theorem chainTop_isNonZero' (hα' : genWeightSpace M α ≠ ⊥) :
    (LieModule.chainTop α β).IsNonZero := by
  by_contra e
  apply hα'
  rw [← add_zero (α : L → R), ← e, LieModule.genWeightSpace_add_chainTop _ _ hα]

