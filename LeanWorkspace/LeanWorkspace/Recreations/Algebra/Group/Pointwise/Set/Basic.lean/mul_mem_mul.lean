import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t := mem_image2_of_mem

