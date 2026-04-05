import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulStrictMono α β]
  {a : α} {b : β}

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 ≤ a • b) :
    0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp only [Decidable.or_iff_not_not_and_not, not_and, not_le]
  refine fun ab nab ↦ hab.not_gt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]

