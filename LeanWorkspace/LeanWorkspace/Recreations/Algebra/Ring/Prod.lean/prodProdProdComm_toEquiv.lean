import Mathlib

variable {R R' S S' T : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

theorem prodProdProdComm_toEquiv :
    (RingEquiv.prodProdProdComm R R' S S' : _ ≃ _) = Equiv.prodProdProdComm R R' S S' := rfl

