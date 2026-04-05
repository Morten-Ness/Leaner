import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem add_le_mul [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b := if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_ge hab)

