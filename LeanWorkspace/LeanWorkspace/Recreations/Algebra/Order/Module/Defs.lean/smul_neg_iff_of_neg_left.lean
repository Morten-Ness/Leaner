import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] [PosSMulReflectLT α β]

theorem smul_neg_iff_of_neg_left (ha : a < 0) : a • b < 0 ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₂ := (0 : β))

