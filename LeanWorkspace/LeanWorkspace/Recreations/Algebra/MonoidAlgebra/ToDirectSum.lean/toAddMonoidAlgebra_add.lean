import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι]

theorem toAddMonoidAlgebra_add [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g := DFinsupp.toFinsupp_add _ _

