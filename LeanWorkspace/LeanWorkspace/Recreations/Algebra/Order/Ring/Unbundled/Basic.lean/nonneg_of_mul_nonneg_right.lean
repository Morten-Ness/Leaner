import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_of_mul_nonneg_right [PosMulStrictMono R]
    (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b := le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_ge h

