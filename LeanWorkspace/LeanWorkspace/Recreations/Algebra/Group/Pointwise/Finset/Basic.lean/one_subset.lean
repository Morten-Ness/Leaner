import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem one_subset : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

-- TODO: This would be a good simp lemma scoped to `Pointwise`, but it seems `@[simp]` can't be
-- scoped

