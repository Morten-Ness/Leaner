import Mathlib

variable {R M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

theorem torsionBySet.mk_smul (I : Ideal R) (b : R) (x : Submodule.torsionBySet R M I) :
    Ideal.Quotient.mk I b • x = b • x := rfl

