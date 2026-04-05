import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι]

theorem toAddMonoidAlgebra_natCast [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ) :
    (n : ⨁ _ : ι, M).toAddMonoidAlgebra = n := DFinsupp.toFinsupp_single _ _

