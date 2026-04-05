import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulStrictMono α β]
  {a : α} {b : β}

theorem smul_nonneg_iff_pos_imp_nonneg : 0 ≤ a • b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := smul_nonneg_iff.trans <| by grind

