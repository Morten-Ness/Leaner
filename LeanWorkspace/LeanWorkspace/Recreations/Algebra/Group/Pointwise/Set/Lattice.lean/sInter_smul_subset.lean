import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem sInter_smul_subset (S : Set (Set α)) (t : Set β) : ⋂₀ S • t ⊆ ⋂ s ∈ S, s • t := image2_sInter_left_subset S t (fun a x => a • x)

