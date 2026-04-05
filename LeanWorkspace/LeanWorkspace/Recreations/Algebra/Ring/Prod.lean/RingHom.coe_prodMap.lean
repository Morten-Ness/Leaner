import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]

variable (f : R →+* R') (g : S →+* S')

theorem coe_prodMap : ⇑(RingHom.prodMap f g) = Prod.map f g := rfl

