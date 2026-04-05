import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] {x : WithTop α} {n : ℕ}

theorem pow_ne_top_iff : x ^ n ≠ ⊤ ↔ x ≠ ⊤ ∨ n = 0 := by simp [pow_eq_top_iff, or_iff_not_imp_left]

