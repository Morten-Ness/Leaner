import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

theorem abs_le_iff_mul_self_le : |a| ≤ |b| ↔ a * a ≤ b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)

