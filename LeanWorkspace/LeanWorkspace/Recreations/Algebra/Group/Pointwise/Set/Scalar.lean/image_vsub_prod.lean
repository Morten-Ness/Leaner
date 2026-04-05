import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem image_vsub_prod : (fun x : β × β ↦ x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t := image_prod _

