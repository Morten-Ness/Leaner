import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

theorem mem_idealizer {x : L} : x ∈ N.idealizer ↔ ∀ m : M, ⁅x, m⁆ ∈ N := Iff.rfl

