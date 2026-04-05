import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι] [Semiring M]

variable [∀ m : M, Decidable (m ≠ 0)]

theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f := Finsupp.toDFinsupp_toFinsupp f

