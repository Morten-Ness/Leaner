import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι] [Semiring M]

variable [∀ m : M, Decidable (m ≠ 0)]

theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ _ : ι, M).toAddMonoidAlgebra = .single i m := DFinsupp.toFinsupp_single i m

