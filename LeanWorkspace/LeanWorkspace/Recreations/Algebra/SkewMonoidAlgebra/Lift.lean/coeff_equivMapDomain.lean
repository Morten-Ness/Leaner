import Mathlib

variable {k G H : Type*}

variable [AddCommMonoid k]

theorem coeff_equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) (b : H) :
    (SkewMonoidAlgebra.equivMapDomain f l).coeff b = l.coeff (f.symm b) := rfl

