import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonpos_of_mul_nonpos_left [PosMulStrictMono R]
    (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 := le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_ge h

