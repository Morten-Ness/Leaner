import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem cmp_mul_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (b * a) (c * a) = cmp c b := (strictAnti_mul_right ha).cmp_map_eq b c

