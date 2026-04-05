import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_le : Subsemigroup.closure s ≤ S ↔ s ⊆ S := ⟨Subset.trans Subsemigroup.subset_closure, fun h => sInf_le h⟩

