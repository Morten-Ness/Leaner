import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty := Nonempty.image2

