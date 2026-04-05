import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem toSubmodule_inj : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N' := LieSubmodule.toSubmodule_injective.eq_iff

