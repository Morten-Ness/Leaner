import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem coe_snd : ⇑(NonUnitalRingHom.snd R S) = Prod.snd := rfl

