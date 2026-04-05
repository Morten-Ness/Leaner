import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftStrictMono R]
    (a : R) : a - 1 < a := sub_lt_iff_lt_add.2 <| lt_add_one a

