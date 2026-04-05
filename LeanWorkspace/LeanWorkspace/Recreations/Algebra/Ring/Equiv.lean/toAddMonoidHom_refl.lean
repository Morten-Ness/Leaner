import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toAddMonoidHom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R := rfl

