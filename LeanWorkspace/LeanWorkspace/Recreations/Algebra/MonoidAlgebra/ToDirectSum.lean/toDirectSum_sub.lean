import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_sub [Ring M] (f g : AddMonoidAlgebra M ι) :
    (f - g).toDirectSum = f.toDirectSum - g.toDirectSum := Finsupp.toDFinsupp_sub _ _

