import Mathlib

variable {K L : Type*}

variable [Semifield K] {a b d : K}

theorem div_add_div (a : K) (c : K) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) := (Commute.all b _).div_add_div (Commute.all _ _) hb hd

