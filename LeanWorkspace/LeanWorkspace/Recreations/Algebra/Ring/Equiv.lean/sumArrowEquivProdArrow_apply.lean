import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem sumArrowEquivProdArrow_apply (x) :
    RingEquiv.sumArrowEquivProdArrow α β R x = Equiv.sumArrowEquivProdArrow α β R x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first

