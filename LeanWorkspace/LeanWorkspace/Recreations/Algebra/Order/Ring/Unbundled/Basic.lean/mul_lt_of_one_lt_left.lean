import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem mul_lt_of_one_lt_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

