import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem pos_of_mul_neg_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (hb : b ≤ 0) : 0 < a := lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

