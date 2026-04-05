import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

theorem coe_chainTop' : (LieModule.chainTop α β : L → R) = LieModule.chainTopCoeff α β • α + β := rfl

