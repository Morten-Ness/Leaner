import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_le_nonneg_of_sq_le_sq [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_ge h

