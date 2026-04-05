import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem iUnion_mul_left_image : ⋃ a ∈ s, (a * ·) '' t = s * t := iUnion_image_left _

