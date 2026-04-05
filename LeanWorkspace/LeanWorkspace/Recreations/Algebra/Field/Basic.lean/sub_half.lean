import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

variable [NeZero (2 : K)]

theorem sub_half (a : K) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves]

