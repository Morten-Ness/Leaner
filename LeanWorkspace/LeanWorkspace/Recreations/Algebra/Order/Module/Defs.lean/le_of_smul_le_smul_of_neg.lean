import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

theorem le_of_smul_le_smul_of_neg [PosSMulReflectLE α β] (h : a • b₁ ≤ a • b₂) (ha : a < 0) :
    b₂ ≤ b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff] at h
  exact le_of_smul_le_smul_of_pos_left h <| neg_pos.2 ha

