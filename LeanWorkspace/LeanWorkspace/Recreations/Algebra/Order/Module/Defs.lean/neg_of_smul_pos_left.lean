import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [LinearOrder α] [LinearOrder β]

theorem neg_of_smul_pos_left [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : b ≤ 0) :
    a < 0 := ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h ↦ h.2.not_ge ha).1

