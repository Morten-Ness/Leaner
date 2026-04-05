import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

variable (hα : α ≠ 0)

theorem genWeightSpace_add_chainTop :
    genWeightSpace M (α + LieModule.chainTop α β : L → R) = ⊥ := by
  rw [LieModule.coe_chainTop', ← add_assoc, ← succ_nsmul',
    LieModule.genWeightSpace_chainTopCoeff_add_one_nsmul_add _ _ hα]

