import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem ker_incl : N.incl.ker = ⊥ := (LieModuleHom.ker_eq_bot N.incl).mpr <| LieSubmodule.injective_incl N

