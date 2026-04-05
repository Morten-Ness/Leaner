import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem mem_weightSpace (χ : L → R) (m : M) : m ∈ LieModule.weightSpace M χ ↔ ∀ x, ⁅x, m⁆ = χ x • m := by
  simp [LieModule.weightSpace]

