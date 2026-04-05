import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

theorem abs_lt_of_sq_lt_sq' (h : a ^ 2 < b ^ 2) (hb : 0 ≤ b) : -b < a ∧ a < b := abs_lt.1 <| abs_lt_of_sq_lt_sq h hb

