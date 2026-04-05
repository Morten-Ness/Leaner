import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

theorem sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b| := by
  simpa only [sq_abs] using sq_lt_sq₀ (abs_nonneg a) (abs_nonneg b)

