import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
    [MulPosStrictMono R] [PosMulStrictMono R]
    (hab : 0 ≤ a * b) : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine Decidable.or_iff_not_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_ge hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)

