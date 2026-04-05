import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_natCast [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) :
    (n : AddMonoidAlgebra M ι).toDirectSum = n := Finsupp.toDFinsupp_single _ _

