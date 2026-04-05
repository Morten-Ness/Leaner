import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonpos_of_mul_nonneg_left [PosMulStrictMono R]
    (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 := le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_ge

