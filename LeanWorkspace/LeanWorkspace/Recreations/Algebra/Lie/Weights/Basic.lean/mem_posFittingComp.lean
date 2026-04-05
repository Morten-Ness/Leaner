import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem mem_posFittingComp (m : M) :
    m ∈ LieModule.posFittingComp R L M ↔ m ∈ ⨆ (x : L), LieModule.posFittingCompOf R M x := by
  rfl

