import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem sub_mul_sub_nonneg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : 0 ≤ (x - a) * (x - b) ↔ x ≤ a ∨ b ≤ x := by
  rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos,
    and_iff_right_of_imp h.trans, and_iff_left_of_imp h.trans', or_comm]

