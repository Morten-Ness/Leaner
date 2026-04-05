import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_of_mul_nonpos_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a := le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

