import Mathlib

theorem addUnits_eq_zero (u : AddUnits ℕ) : u = 0 := by
  ext
  exact (Nat.eq_zero_of_add_eq_zero u.val_neg).1
