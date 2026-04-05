import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [LinearOrder α] [LinearOrder β]

theorem neg_iff_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) :
    a < 0 ↔ b < 0 := ⟨neg_of_smul_pos_right hab ∘ le_of_lt, neg_of_smul_pos_left hab ∘ le_of_lt⟩

