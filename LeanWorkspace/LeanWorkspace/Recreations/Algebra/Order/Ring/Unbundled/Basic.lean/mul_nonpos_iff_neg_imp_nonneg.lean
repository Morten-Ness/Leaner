import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem mul_nonpos_iff_neg_imp_nonneg [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [← neg_nonneg, ← neg_mul, mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

