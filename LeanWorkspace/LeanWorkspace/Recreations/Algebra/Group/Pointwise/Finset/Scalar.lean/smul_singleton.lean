import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) := image₂_singleton_right

