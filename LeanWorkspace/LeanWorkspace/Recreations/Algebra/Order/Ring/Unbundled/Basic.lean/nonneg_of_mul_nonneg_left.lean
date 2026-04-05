import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_of_mul_nonneg_left [MulPosStrictMono R]
    (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a := le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_ge h

