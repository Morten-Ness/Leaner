import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

omit [IsOrderedRing α] in
theorem abs_sq (x : α) : |x ^ 2| = x ^ 2 := by simpa only [sq] using abs_mul_self x

