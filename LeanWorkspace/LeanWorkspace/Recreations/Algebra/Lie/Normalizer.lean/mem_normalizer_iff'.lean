import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (H : LieSubalgebra R L)

theorem mem_normalizer_iff' (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅y, x⁆ ∈ H := by
  rw [Subtype.forall']; rfl

