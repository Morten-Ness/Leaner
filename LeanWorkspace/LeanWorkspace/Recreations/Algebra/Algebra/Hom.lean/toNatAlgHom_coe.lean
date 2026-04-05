import Mathlib

variable {R S : Type*}

theorem toNatAlgHom_coe [Semiring R] [Semiring S] (f : R →+* S) :
    ⇑f.toNatAlgHom = ⇑f := rfl

