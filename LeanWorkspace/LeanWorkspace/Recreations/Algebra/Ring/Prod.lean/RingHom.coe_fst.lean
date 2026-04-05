import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

theorem coe_fst : ⇑(RingHom.fst R S) = Prod.fst := rfl

