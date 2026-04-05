import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulZeroClass α β]

variable [Preorder α] [Preorder β]

theorem smul_neg_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b < 0 ↔ b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₂ := (0 : β))

