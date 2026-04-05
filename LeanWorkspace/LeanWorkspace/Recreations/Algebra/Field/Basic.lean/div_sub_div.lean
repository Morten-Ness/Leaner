import Mathlib

variable {K L : Type*}

variable [Field K]

theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - b * c) / (b * d) := (Commute.all b _).div_sub_div (Commute.all _ _) hb hd

