import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonpos_of_mul_nonpos_right [PosMulStrictMono R]
    (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 := le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_ge h

