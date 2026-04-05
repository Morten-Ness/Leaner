import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem add_le_mul' [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a := (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

