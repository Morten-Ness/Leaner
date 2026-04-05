import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ Subsemigroup.closure s) : Subsemigroup.closure s = S := le_antisymm (Subsemigroup.closure_le.2 h₁) h₂

