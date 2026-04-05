import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem mem_map (x : L₂) : x ∈ K.map f ↔ ∃ y : L, y ∈ K ∧ f y = x := Submodule.mem_map

-- TODO Rename and state for homs instead of equivs.

