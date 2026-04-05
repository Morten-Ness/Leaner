import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty := Nonempty.of_image2_right

