import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem cmp_mul_pos_right [MulPosStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (b * a) (c * a) = cmp b c := (strictMono_mul_right_of_pos ha).cmp_map_eq b c

