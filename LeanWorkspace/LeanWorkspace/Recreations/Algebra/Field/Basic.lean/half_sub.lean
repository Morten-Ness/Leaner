import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

variable [NeZero (2 : K)]

theorem half_sub (a : K) : a / 2 - a = -(a / 2) := by rw [← neg_sub, sub_half]

