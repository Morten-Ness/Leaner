import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem subset_smul {s : Set α} {t : Set β} :
    ↑u ⊆ s • t → ∃ (s' : Finset α) (t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' := subset_set_image₂

