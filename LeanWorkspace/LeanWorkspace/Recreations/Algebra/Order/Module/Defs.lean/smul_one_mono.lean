import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero β]

theorem smul_one_mono [One β] [ZeroLEOneClass β] [SMulPosMono α β] :
    Monotone (fun x : α ↦ x • (1 : β)) := fun _ _ ha ↦ smul_le_smul_of_nonneg_right ha zero_le_one

