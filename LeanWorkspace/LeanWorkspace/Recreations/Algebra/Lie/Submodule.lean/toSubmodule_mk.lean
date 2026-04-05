import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem toSubmodule_mk (p : Submodule R M) (h) :
    (({ p with lie_mem := h } : LieSubmodule R L M) : Submodule R M) = p := by cases p; rfl

