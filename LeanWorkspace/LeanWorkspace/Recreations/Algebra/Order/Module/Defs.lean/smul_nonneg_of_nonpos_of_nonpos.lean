import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

omit [IsOrderedRing α] in
theorem smul_nonneg_of_nonpos_of_nonpos [SMulPosMono α β] (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a • b := smul_nonpos_of_nonpos_of_nonneg (β := βᵒᵈ) ha hb

