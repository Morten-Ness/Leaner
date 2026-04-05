import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

theorem modOf_apply_of_not_exists_add (x : k[G]) (g : G) (g' : G)
    (h : ¬∃ d, g' = g + d) : (x %ᵒᶠ g) g' = x g' := by
  classical exact Finsupp.filter_apply_pos _ _ h

