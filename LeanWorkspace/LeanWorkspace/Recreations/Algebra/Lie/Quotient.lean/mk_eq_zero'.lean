import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mk_eq_zero' {m : M} : LieSubmodule.Quotient.mk (N := N) m = 0 ↔ m ∈ N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule

