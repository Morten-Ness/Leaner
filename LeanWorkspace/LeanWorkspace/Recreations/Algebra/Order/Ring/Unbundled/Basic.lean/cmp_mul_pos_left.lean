import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem cmp_mul_pos_left [PosMulStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (a * b) (a * c) = cmp b c := (strictMono_mul_left_of_pos ha).cmp_map_eq b c

