import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} := image₂_singleton

