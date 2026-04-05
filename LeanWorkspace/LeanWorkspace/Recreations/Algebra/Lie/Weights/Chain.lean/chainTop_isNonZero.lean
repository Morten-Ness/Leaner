import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

theorem chainTop_isNonZero (α β : Weight R L M) (hα : α.IsNonZero) :
    (LieModule.chainTop α β).IsNonZero := LieModule.chainTop_isNonZero' α β hα α.2

