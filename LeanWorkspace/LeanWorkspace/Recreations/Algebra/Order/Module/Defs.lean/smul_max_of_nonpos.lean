import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]

variable [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulMono α β]
  {a : α} {b b₁ b₂ : β}

theorem smul_max_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • max b₁ b₂ = min (a • b₁) (a • b₂) := (antitone_smul_left ha : Antitone (_ : β → β)).map_max

