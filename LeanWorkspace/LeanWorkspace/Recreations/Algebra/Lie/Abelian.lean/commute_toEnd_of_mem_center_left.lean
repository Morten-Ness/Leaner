import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable {x : L} (hx : x ∈ LieAlgebra.center R L) (y : L)

theorem commute_toEnd_of_mem_center_left :
    Commute (toEnd R L M x) (toEnd R L M y) := by
  rw [Commute.symm_iff, commute_iff_lie_eq, ← LieHom.map_lie, hx y, map_zero]

