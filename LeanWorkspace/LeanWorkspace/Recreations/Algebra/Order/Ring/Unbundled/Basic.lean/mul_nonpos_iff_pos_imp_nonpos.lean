import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem mul_nonpos_iff_pos_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← mul_neg, mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

