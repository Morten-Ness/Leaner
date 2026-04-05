import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum := Finsupp.toDFinsupp_add _ _

