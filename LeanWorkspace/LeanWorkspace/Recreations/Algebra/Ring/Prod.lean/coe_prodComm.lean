import Mathlib

variable {R R' S S' T : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

theorem coe_prodComm : ⇑(RingEquiv.prodComm : R × S ≃+* S × R) = Prod.swap := rfl

