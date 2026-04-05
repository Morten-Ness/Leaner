import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty := Nonempty.of_image2_left

