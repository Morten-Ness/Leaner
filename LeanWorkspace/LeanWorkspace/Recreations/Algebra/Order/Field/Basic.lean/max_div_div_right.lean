import Mathlib

variable {ι α β : Type*}

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d e : α}

theorem max_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : max (a / c) (b / c) = max a b / c := (monotone_div_right_of_nonneg hc).map_max.symm

