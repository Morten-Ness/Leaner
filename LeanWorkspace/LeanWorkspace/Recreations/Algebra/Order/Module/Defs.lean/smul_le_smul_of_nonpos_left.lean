import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

variable [PosSMulMono α β]

theorem smul_le_smul_of_nonpos_left (h : b₁ ≤ b₂) (ha : a ≤ 0) : a • b₂ ≤ a • b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff]
  exact smul_le_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

