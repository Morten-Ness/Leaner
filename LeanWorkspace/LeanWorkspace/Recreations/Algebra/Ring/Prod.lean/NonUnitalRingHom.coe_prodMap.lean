import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]

variable (f : R →ₙ+* R') (g : S →ₙ+* S')

theorem coe_prodMap : ⇑(NonUnitalRingHom.prodMap f g) = Prod.map f g := rfl

