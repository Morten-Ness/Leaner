import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_lt_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b c : R} (h : c < 0) : a * c < b * c ↔ b < a := (strictAnti_mul_right h).lt_iff_gt

