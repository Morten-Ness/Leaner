import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem lt_mul_of_lt_one_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

