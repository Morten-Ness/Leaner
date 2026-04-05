import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [LinearOrder α] [LinearOrder β]

theorem neg_of_smul_neg_right' [PosSMulMono α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 := lt_of_not_ge fun ha ↦ (smul_nonneg ha hb).not_gt h

