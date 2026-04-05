import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem inter_smul_union_subset_union [DecidableEq α] : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ := image₂_inter_union_subset_union

