import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

theorem modOf_apply_of_exists_add (x : k[G]) (g : G) (g' : G)
    (h : ∃ d, g' = g + d) : (x %ᵒᶠ g) g' = 0 := by
  classical exact Finsupp.filter_apply_neg _ _ <| by rwa [Classical.not_not]

