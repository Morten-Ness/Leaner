import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : LieSubmodule R L M → Submodule R M) := fun x y h ↦ by
  cases x; cases y; congr

