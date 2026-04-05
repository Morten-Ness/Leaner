import Mathlib

variable {R S : Type*}

theorem toIntAlgHom_apply [Ring R] [Ring S] (f : R →+* S) (x : R) :
    f.toIntAlgHom x = f x := rfl

