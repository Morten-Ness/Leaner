import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem max_mul_of_nonneg [MulPosMono R]
    (a b : R) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) := (monotone_mul_right_of_nonneg hc).map_max

