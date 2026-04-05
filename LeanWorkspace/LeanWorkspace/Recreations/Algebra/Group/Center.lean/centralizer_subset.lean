import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_subset (h : S ⊆ T) : Set.centralizer T ⊆ Set.centralizer S := fun _ ht s hs ↦ ht s (h hs)

