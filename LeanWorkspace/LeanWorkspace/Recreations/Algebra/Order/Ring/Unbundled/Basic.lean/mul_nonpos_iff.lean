import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem mul_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff (R := R), neg_nonneg, neg_nonpos]

