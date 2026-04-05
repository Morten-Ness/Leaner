import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toMonoidHom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R := rfl

