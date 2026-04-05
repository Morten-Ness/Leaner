import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem cmp_mul_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (a * b) (a * c) = cmp c b := (strictAnti_mul_left ha).cmp_map_eq b c

