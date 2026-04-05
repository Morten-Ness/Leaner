import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem center_subset_centralizer (S : Set M) : Set.center M ⊆ S.centralizer := fun _ hx m _ ↦ (hx.comm m).symm

