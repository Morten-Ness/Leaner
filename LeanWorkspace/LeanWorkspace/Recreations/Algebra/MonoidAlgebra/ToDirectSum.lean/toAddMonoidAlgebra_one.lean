import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι]

theorem toAddMonoidAlgebra_one [Zero ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    (1 : ⨁ _ : ι, M).toAddMonoidAlgebra = 1 := DFinsupp.toFinsupp_single _ _

