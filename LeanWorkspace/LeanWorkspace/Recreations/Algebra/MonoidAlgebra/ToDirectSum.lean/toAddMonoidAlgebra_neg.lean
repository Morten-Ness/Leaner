import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

variable [DecidableEq ι]

theorem toAddMonoidAlgebra_neg [Ring M] [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) :
    (-f).toAddMonoidAlgebra = - toAddMonoidAlgebra f := DFinsupp.toFinsupp_neg _

