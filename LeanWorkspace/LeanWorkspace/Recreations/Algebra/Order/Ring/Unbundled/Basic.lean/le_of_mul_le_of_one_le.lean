import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem le_of_mul_le_of_one_le
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrictMono R] [PosMulMono R]
    {a b c : R} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b := le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) <| zero_lt_one.trans_le hc

