import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem lt_of_mul_lt_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : a * c < b * c) (hc : c ≤ 0) : b < a := (antitone_mul_right hc).reflect_lt h

