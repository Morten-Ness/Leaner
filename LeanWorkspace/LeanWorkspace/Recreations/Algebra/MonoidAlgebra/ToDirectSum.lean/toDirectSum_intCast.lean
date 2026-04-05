import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_intCast [DecidableEq ι] [AddMonoid ι] [Ring M] (z : ℤ) :
    (Int.cast z : AddMonoidAlgebra M ι).toDirectSum = z := Finsupp.toDFinsupp_single _ _

