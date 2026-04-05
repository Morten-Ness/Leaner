import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem smul_finset_subset_smul {s : Finset α} : a ∈ s → a • t ⊆ s • t := image_subset_image₂_right

