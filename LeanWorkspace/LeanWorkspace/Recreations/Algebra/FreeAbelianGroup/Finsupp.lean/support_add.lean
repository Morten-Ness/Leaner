import Mathlib

open scoped Classical

variable {X : Type*}

theorem support_add (a b : FreeAbelianGroup X) : FreeAbelianGroup.support (a + b) ⊆ a.support ∪ b.support := by
  simp only [FreeAbelianGroup.support, map_add]
  apply Finsupp.support_add

