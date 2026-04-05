import Mathlib

variable {n : ℕ}

theorem coe_sub_one (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  exact val_sub_one_of_ne_zero h

