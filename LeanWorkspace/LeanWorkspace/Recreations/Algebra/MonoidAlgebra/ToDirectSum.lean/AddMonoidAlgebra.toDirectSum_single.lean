import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι] [Semiring M]

theorem AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) : toDirectSum (single i m) = .of _ i m := Finsupp.toDFinsupp_single i m

