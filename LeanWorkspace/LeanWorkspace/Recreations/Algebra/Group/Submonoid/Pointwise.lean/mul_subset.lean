import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

theorem mul_subset {S : Submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S := mul_subset_iff.2 fun _x hx _y hy ↦ mul_mem (hs hx) (ht hy)

