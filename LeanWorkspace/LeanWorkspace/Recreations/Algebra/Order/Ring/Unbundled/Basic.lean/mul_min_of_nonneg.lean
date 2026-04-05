import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_min_of_nonneg [PosMulMono R]
    (b c : R) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) := (monotone_mul_left_of_nonneg ha).map_min

