import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

