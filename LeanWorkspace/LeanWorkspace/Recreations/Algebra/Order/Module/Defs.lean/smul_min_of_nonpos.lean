import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulMono α β]
  {a : α} {b b₁ b₂ : β}

theorem smul_min_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • min b₁ b₂ = max (a • b₁) (a • b₂) := (antitone_smul_left ha : Antitone (_ : β → β)).map_min

