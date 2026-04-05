import Mathlib

variable {K L : Type*}

variable [Semifield K] {a b d : K}

theorem one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := (Commute.all a _).one_div_add_one_div ha hb

