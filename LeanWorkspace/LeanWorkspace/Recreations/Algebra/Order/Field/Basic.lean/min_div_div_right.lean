import Mathlib

variable {ι α β : Type*}

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d e : α}

theorem min_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : min (a / c) (b / c) = min a b / c := (monotone_div_right_of_nonneg hc).map_min.symm

