import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem lt_mul_of_lt_one_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

