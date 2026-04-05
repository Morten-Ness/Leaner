import Mathlib

variable {k G H : Type*}

variable [AddCommMonoid k]

theorem toFinsupp_equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) :
    (SkewMonoidAlgebra.equivMapDomain f l).toFinsupp = Finsupp.equivMapDomain f l.toFinsupp := rfl

