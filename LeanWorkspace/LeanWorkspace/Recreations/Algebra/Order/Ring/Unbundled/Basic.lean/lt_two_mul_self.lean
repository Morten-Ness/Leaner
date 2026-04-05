import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem lt_two_mul_self [ZeroLEOneClass R] [MulPosStrictMono R] [NeZero (1 : R)]
    [AddLeftStrictMono R] (ha : 0 < a) : a < 2 * a := lt_mul_of_one_lt_left ha one_lt_two

