import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero α]

theorem smul_le_smul_iff_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a • b₁ ≤ a • b₂ ↔ b₁ ≤ b₂ := ⟨fun h ↦ le_of_smul_le_smul_left h ha, fun h ↦ smul_le_smul_of_nonneg_left h ha.le⟩

