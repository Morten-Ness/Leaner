import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem image_div_product : ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / t := rfl

