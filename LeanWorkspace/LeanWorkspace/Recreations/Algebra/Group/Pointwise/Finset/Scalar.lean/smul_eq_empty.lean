import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

