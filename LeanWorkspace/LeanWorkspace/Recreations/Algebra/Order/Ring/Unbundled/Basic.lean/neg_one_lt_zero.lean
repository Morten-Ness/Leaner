import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem neg_one_lt_zero
    [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStrictMono R] :
    -1 < (0 : R) := neg_lt_zero.2 zero_lt_one

