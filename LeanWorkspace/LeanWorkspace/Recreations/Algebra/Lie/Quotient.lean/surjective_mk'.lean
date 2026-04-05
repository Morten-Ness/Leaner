import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

theorem surjective_mk' : Function.Surjective (LieSubmodule.Quotient.mk' N) := Quot.mk_surjective

