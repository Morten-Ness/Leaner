import Mathlib

variable {R M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

theorem torsionBy.mk_smul (a b : R) (x : Submodule.torsionBy R M a) :
    Ideal.Quotient.mk (R ∙ a) b • x = b • x := rfl

