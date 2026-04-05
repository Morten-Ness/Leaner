import Mathlib

variable {R : Type*}

variable [Monoid R] {a b : R} {n : ℕ}

theorem IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]; exact .of_mul
  mpr := .pow n

