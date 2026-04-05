import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem smul_sInter_subset (s : Set α) (T : Set (Set β)) : s • ⋂₀ T ⊆ ⋂ t ∈ T, s • t := image2_sInter_right_subset s T (fun a x => a • x)

