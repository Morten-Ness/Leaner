import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem mul_nonneg_iff_neg_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 ≤ a * b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [← neg_mul_neg, mul_nonneg_iff_pos_imp_nonneg (R := R)]; simp only [neg_pos, neg_nonneg]

