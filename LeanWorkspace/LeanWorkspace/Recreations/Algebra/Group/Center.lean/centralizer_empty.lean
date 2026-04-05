import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_empty : (∅ : Set M).centralizer = ⊤ := by simp [Set.centralizer]

