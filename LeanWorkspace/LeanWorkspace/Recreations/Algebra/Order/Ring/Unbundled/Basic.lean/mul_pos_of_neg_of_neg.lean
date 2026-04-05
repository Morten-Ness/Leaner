import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b : R} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

