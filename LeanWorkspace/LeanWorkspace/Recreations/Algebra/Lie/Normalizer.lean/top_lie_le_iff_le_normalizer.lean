import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

theorem top_lie_le_iff_le_normalizer (N' : LieSubmodule R L M) :
    ⁅(⊤ : LieIdeal R L), N⁆ ≤ N' ↔ N ≤ N'.normalizer := by rw [lie_le_iff]; tauto

