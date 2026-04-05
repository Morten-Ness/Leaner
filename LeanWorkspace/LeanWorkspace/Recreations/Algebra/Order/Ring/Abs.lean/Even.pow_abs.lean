import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

theorem Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n := by
  rw [← abs_pow, abs_eq_self]; exact hn.pow_nonneg _

