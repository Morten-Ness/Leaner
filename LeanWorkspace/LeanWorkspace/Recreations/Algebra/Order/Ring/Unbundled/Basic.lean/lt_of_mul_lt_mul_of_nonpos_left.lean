import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem lt_of_mul_lt_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : c * a < c * b) (hc : c ≤ 0) : b < a := (antitone_mul_left hc).reflect_lt h

