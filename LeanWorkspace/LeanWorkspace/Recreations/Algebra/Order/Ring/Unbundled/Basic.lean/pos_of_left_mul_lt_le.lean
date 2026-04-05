import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem pos_of_left_mul_lt_le [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddRightReflectLE R]
    (h : b * a < c * a) (hbc : b ≤ c) :
    0 < a := by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_right hbc ha]

