import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_neg [Ring M] (f : AddMonoidAlgebra M ι) :
    (-f).toDirectSum = - f.toDirectSum := Finsupp.toDFinsupp_neg _

