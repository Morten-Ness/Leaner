import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

theorem toEnd_comp_mk' (x : L) :
    LieModule.toEnd R L (M ⧸ N) x ∘ₗ LieSubmodule.Quotient.mk' N = LieSubmodule.Quotient.mk' N ∘ₗ LieModule.toEnd R L M x := rfl

