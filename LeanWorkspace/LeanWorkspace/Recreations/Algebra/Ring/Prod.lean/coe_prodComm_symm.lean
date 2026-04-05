import Mathlib

variable {R R' S S' T : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

theorem coe_prodComm_symm : ⇑(RingEquiv.prodComm : R × S ≃+* S × R).symm = Prod.swap := rfl

