import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_one [DecidableEq ι] [Zero ι] [Semiring M] :
    (1 : AddMonoidAlgebra M ι).toDirectSum = 1 := Finsupp.toDFinsupp_single _ _

