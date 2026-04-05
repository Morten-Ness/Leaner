import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_union : Set.centralizer (S ∪ T) = Set.centralizer S ∩ Set.centralizer T := by
  simp [Set.centralizer, or_imp, forall_and, setOf_and]

