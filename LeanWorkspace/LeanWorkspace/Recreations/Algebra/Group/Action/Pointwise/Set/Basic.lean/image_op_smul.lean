import Mathlib

open scoped Pointwise RightActions

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem image_op_smul : (op '' s) • t = t * s := by
  rw [← image2_smul, ← image2_mul, image2_image_left, image2_swap]
  rfl

