import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] [PosSMulReflectLT α β]

theorem smul_lt_smul_iff_of_neg_left (ha : a < 0) : a • b₁ < a • b₂ ↔ b₂ < b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos_left (neg_pos_of_neg ha)

