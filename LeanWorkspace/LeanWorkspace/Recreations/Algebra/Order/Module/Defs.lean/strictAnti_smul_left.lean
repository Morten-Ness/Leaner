import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β]

theorem strictAnti_smul_left (ha : a < 0) : StrictAnti ((a • ·) : β → β) := fun _ _ h ↦ smul_lt_smul_of_neg_left h ha

