import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

theorem abs_le_of_sq_le_sq' (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : -b ≤ a ∧ a ≤ b := abs_le.1 <| abs_le_of_sq_le_sq h hb

