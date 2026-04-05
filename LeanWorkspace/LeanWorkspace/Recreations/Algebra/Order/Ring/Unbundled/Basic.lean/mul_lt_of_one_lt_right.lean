import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem mul_lt_of_one_lt_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

