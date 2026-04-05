import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem image_smul_prod : (fun x : α × β ↦ x.fst • x.snd) '' s ×ˢ t = s • t := image_prod _

