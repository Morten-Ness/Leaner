import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonpos_of_mul_nonneg_right [MulPosStrictMono R]
    (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 := le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_ge

