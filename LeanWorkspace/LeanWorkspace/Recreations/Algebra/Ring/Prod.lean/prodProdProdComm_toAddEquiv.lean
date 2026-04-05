import Mathlib

variable {R R' S S' T : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

theorem prodProdProdComm_toAddEquiv :
    (RingEquiv.prodProdProdComm R R' S S' : _ ≃+ _) = AddEquiv.prodProdProdComm R R' S S' := rfl

