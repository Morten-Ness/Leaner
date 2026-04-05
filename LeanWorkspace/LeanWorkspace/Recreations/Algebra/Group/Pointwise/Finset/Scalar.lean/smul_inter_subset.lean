import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ := image₂_inter_subset_right

