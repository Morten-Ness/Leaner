import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem posFittingCompOf_le_posFittingComp (x : L) :
    LieModule.posFittingCompOf R M x ≤ LieModule.posFittingComp R L M := by
  rw [LieModule.posFittingComp]; exact le_iSup (LieModule.posFittingCompOf R M) x

