import Mathlib

variable {R : Type u}

variable [Ring R] {a : R} {n : ℕ}

variable [NoZeroDivisors R]

theorem sq_ne_one_iff : a ^ 2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 := sq_eq_one_iff.not.trans not_or

