import Mathlib

open scoped symmDiff

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem apply_mulIndicator_symmDiff {g : G → β} (hg : ∀ x, g x⁻¹ = g x)
    (s t : Set α) (f : α → G) (x : α) :
    g (mulIndicator (s ∆ t) f x) = g (mulIndicator s f x / mulIndicator t f x) := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [mem_symmDiff, *]

