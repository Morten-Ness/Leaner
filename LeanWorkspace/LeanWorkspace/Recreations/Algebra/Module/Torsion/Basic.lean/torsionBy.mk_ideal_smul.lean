import Mathlib

variable {R M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

theorem torsionBy.mk_ideal_smul (a b : R) (x : Submodule.torsionBy R M a) :
    (Ideal.Quotient.mk (Ideal.span {a})) b • x = b • x := rfl

