import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

theorem lt_of_smul_lt_smul_of_nonpos [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : a ≤ 0) :
    b₂ < b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

