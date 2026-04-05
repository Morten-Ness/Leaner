import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem Even.sub_odd (h : n ≤ m) (hm : Even m) (hn : Odd n) : Odd (m - n) := by grind

