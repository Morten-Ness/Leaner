import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

