import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι]

theorem toAddMonoidAlgebra_ofNat [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ)
    [n.AtLeastTwo] :
    (ofNat(n) : ⨁ _ : ι, M).toAddMonoidAlgebra = ofNat(n) := DFinsupp.toFinsupp_single _ _

