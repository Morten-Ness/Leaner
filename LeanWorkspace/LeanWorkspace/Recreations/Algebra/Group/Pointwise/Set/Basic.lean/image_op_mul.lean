import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem image_op_mul : op '' (s * t) = op '' t * op '' s := image_image2_antidistrib op_mul

