import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem mul_neg_iff [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftReflectLT R] [AddLeftStrictMono R] :
    a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff (R := R), neg_pos, neg_lt_zero]

