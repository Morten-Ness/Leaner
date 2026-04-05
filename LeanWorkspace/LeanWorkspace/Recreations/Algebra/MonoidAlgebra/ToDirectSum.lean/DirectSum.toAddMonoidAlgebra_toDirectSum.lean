import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι] [Semiring M]

variable [∀ m : M, Decidable (m ≠ 0)]

theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f := (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) :)

