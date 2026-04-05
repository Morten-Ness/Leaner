import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

omit [IsOrderedRing α] in
theorem abs_mul_self (a : α) : |a * a| = a * a := by simp

