import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem vsub_sInter_subset (s : Set β) (T : Set (Set β)) : s -ᵥ ⋂₀ T ⊆ ⋂ t ∈ T, s -ᵥ t := image2_sInter_subset_right ..

