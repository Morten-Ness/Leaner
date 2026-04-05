import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι]

theorem toAddMonoidAlgebra_intCast [AddMonoid ι] [Ring M] [∀ m : M, Decidable (m ≠ 0)] (z : ℤ) :
    (z : ⨁ _ : ι, M).toAddMonoidAlgebra = z := DFinsupp.toFinsupp_single _ _

