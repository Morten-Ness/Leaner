import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable {N : LieSubmodule R L M} {x : L}

theorem coe_map_toEnd_le :
    (N : Submodule R M).map (LieModule.toEnd R L M x) ≤ N := by
  rintro n ⟨m, hm, rfl⟩
  exact N.lie_mem hm

