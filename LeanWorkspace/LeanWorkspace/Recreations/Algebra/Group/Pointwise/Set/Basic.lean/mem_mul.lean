import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem mem_mul : a ∈ s * t ↔ ∃ x ∈ s, ∃ y ∈ t, x * y = a := Iff.rfl

