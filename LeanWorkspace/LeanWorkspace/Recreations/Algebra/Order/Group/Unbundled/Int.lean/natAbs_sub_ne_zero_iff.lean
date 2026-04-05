import Mathlib

theorem natAbs_sub_ne_zero_iff {i j : ℤ} : natAbs (i - j) ≠ 0 ↔ i ≠ j := Nat.ne_zero_iff_zero_lt.trans Int.natAbs_sub_pos_iff

