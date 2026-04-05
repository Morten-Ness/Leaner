import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} := image2_singleton

