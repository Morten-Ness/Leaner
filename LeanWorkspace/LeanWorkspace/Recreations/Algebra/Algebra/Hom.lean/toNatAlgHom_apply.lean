import Mathlib

variable {R S : Type*}

theorem toNatAlgHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    f.toNatAlgHom x = f x := rfl

