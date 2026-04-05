import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toRingHom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R := rfl

