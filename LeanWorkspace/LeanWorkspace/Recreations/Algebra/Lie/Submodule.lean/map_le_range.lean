import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem map_le_range {M' : Type*}
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] (f : M →ₗ⁅R,L⁆ M') :
    N.map f ≤ f.range := by
  rw [← LieModuleHom.map_top]
  exact LieSubmodule.map_mono le_top

