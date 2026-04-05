import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

variable [PosSMulMono α β]

theorem antitone_smul_left (ha : a ≤ 0) : Antitone ((a • ·) : β → β) := fun _ _ h ↦ smul_le_smul_of_nonpos_left h ha

