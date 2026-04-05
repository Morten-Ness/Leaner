import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem coe_fst : ⇑(NonUnitalRingHom.fst R S) = Prod.fst := rfl

