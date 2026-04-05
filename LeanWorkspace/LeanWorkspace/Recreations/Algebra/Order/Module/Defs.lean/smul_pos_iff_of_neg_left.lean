import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] [PosSMulReflectLT α β]

theorem smul_pos_iff_of_neg_left (ha : a < 0) : 0 < a • b ↔ b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₁ := (0 : β))

alias ⟨_, smul_pos_of_neg_of_neg⟩ := smul_pos_iff_of_neg_left

