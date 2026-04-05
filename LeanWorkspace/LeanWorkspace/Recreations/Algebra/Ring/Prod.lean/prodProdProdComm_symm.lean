import Mathlib

variable {R R' S S' T : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

theorem prodProdProdComm_symm : (RingEquiv.prodProdProdComm R R' S S').symm = RingEquiv.prodProdProdComm R S R' S' := rfl

