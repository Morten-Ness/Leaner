import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s ⊆ t) :
    t.mulIndicator f = f := by
  rw [Set.mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2

