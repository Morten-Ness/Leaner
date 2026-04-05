import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

theorem coe_snd : ⇑(RingHom.snd R S) = Prod.snd := rfl

