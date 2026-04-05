import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem sumArrowEquivProdArrow_symm_apply (x : (α → R) × (β → R)) :
    (RingEquiv.sumArrowEquivProdArrow α β R).symm x = (Equiv.sumArrowEquivProdArrow α β R).symm x := rfl

