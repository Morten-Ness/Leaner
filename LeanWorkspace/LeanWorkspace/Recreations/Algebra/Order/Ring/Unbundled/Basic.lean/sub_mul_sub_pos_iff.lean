import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem sub_mul_sub_pos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : 0 < (x - a) * (x - b) ↔ x < a ∨ b < x := by
  rw [mul_pos_iff, sub_pos, sub_pos, sub_neg, sub_neg, and_iff_right_of_imp h.trans_lt,
    and_iff_left_of_imp h.trans_lt', or_comm]

