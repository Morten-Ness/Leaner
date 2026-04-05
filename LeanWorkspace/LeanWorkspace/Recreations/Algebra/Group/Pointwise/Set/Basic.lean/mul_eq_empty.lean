import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

