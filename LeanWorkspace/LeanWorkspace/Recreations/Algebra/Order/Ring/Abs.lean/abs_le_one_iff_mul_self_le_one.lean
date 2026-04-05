import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

theorem abs_le_one_iff_mul_self_le_one : |a| ≤ 1 ↔ a * a ≤ 1 := by
  simpa only [abs_one, one_mul] using abs_le_iff_mul_self_le (a := a) (b := 1)

