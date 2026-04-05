import Mathlib

variable {R R' S S' T : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

theorem snd_comp_coe_prodComm :
    (RingHom.snd S R).comp ↑(RingEquiv.prodComm : R × S ≃+* S × R) = RingHom.fst R S := RingHom.ext fun _ => rfl

