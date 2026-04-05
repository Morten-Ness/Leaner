import Mathlib

variable {R S : Type*}

theorem toIntAlgHom_coe [Ring R] [Ring S] (f : R →+* S) :
    ⇑f.toIntAlgHom = ⇑f := rfl

