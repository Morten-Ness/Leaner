import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)

variable (f : M →ₗ⁅R,L⁆ M₂)

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

theorem map_bracket_eq [LieModule R L M] : map f ⁅I, N⁆ = ⁅I, map f N⁆ := by
  rw [← toSubmodule_inj, toSubmodule_map, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LieSubmodule.lieIdeal_oper_eq_linear_span, Submodule.map_span]
  congr
  ext m
  simp

