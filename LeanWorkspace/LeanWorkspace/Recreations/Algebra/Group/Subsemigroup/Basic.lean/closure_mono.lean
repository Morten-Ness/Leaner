import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : Subsemigroup.closure s ≤ Subsemigroup.closure t := Subsemigroup.closure_le.2 <| Subset.trans h Subsemigroup.subset_closure

