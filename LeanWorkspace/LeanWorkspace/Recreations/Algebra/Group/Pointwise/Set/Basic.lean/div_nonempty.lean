import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

