import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_of_mul_nonpos_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b := le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

