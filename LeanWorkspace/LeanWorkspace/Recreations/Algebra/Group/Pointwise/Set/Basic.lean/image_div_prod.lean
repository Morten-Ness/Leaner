import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t := image_prod _

