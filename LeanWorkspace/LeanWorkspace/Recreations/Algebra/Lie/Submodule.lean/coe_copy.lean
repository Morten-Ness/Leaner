import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s := rfl

