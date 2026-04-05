import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

theorem abs_pow_eq_one (a : α) (h : n ≠ 0) : |a ^ n| = 1 ↔ |a| = 1 := by
  convert pow_left_inj₀ (abs_nonneg a) zero_le_one h
  exacts [(pow_abs _ _).symm, (one_pow _).symm]

