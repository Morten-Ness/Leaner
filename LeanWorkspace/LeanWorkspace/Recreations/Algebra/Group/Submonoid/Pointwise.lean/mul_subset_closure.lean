import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

theorem mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ Submonoid.closure u := Submonoid.mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

