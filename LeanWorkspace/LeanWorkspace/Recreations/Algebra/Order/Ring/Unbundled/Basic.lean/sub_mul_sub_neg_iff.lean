import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem sub_mul_sub_neg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : (x - a) * (x - b) < 0 ↔ a < x ∧ x < b := by
  rw [mul_neg_iff, sub_pos, sub_pos, sub_neg, sub_neg, or_iff_left_iff_imp, and_comm]
  exact And.imp h.trans_lt h.trans_lt'

