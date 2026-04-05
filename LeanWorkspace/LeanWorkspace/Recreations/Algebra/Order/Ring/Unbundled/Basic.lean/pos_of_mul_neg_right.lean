import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem pos_of_mul_neg_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (ha : a ≤ 0) : 0 < b := lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

