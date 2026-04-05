import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

theorem image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t := rfl

