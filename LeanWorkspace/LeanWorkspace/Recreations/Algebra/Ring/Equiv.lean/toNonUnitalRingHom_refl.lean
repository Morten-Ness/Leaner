import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

theorem toNonUnitalRingHom_refl :
    (RingEquiv.refl R).toNonUnitalRingHom = NonUnitalRingHom.id R := rfl

