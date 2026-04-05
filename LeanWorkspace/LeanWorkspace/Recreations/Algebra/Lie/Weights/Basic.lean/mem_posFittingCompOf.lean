import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem mem_posFittingCompOf (x : L) (m : M) :
    m ∈ LieModule.posFittingCompOf R M x ↔ ∀ (k : ℕ), ∃ n, (toEnd R L M x ^ k) n = m := by
  simp [LieModule.posFittingCompOf]

