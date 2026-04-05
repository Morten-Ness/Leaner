import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem inter_smul_subset [DecidableEq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image₂_inter_subset_left

