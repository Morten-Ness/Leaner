import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem iUnion_op_smul_set (s t : Set α) : ⋃ a ∈ t, MulOpposite.op a • s = s * t := iUnion_image_right _

