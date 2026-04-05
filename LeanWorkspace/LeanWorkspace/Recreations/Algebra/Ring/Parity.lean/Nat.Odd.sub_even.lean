import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem Odd.sub_even (h : n ≤ m) (hm : Odd m) (hn : Even n) : Odd (m - n) := by grind

