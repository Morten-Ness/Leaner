import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

theorem mk_bracket (x y : L) : LieSubmodule.Quotient.mk ⁅x, y⁆ = ⁅(LieSubmodule.Quotient.mk x : L ⧸ I), (LieSubmodule.Quotient.mk y : L ⧸ I)⁆ := rfl

