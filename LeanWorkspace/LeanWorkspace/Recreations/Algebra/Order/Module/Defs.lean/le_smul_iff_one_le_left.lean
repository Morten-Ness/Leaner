import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Monoid α] [Zero β] [MulAction α β]

variable [Preorder α] [Preorder β]

theorem le_smul_iff_one_le_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    b ≤ a • b ↔ 1 ≤ a := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

