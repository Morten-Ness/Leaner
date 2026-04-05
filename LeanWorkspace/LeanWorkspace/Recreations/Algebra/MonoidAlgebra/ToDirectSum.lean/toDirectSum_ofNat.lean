import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_ofNat [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : AddMonoidAlgebra M ι).toDirectSum = ofNat(n) := Finsupp.toDFinsupp_single _ _

