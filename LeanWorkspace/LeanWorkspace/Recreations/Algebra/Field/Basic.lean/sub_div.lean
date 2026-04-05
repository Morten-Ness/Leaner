import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c := (div_sub_div_same _ _ _).symm

