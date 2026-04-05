import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero β]

theorem smul_le_smul_iff_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a₁ • b ≤ a₂ • b ↔ a₁ ≤ a₂ := ⟨fun h ↦ le_of_smul_le_smul_right h hb, fun ha ↦ smul_le_smul_of_nonneg_right ha hb.le⟩

