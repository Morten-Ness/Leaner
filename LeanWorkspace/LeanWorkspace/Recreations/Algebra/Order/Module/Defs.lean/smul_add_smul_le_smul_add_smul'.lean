import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulMono α β] {a₁ a₂ : α} {b₁ b₂ : β}

theorem smul_add_smul_le_smul_add_smul' (ha : a₂ ≤ a₁) (hb : b₂ ≤ b₁) :
    a₁ • b₂ + a₂ • b₁ ≤ a₁ • b₁ + a₂ • b₂ := by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_le_smul_add_smul ha hb

