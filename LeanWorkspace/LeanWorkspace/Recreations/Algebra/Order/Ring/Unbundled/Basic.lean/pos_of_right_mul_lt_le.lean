import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem pos_of_right_mul_lt_le [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : a * b < a * c) (hbc : b ≤ c) :
    0 < a := by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_left hbc ha]

