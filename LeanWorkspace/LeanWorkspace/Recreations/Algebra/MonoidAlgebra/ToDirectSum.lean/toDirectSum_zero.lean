import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 := Finsupp.toDFinsupp_zero

