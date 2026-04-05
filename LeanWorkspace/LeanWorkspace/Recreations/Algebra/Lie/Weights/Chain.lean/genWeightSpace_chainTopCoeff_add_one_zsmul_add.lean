import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

variable (hα : α ≠ 0)

theorem genWeightSpace_chainTopCoeff_add_one_zsmul_add :
    genWeightSpace M ((LieModule.chainTopCoeff α β + 1 : ℤ) • α + β : L → R) = ⊥ := by
  rw [← LieModule.genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα, ← Nat.cast_smul_eq_nsmul ℤ,
    Nat.cast_add, Nat.cast_one]

