import Mathlib

variable {R R' S S' T : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

theorem fst_comp_coe_prodComm :
    (RingHom.fst S R).comp ↑(RingEquiv.prodComm : R × S ≃+* S × R) = RingHom.snd R S := RingHom.ext fun _ => rfl

