import Mathlib

variable {n : ℕ}

theorem sub_one_lt_iff {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k := not_iff_not.1 <| by simp only [lt_def, not_lt, val_fin_le, le_sub_one_iff, le_zero_iff]

