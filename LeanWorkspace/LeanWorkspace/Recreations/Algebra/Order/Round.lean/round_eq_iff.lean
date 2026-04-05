import Mathlib

variable {F α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_eq_iff {x : α} {n : ℤ} : round x = n ↔ x ∈ Ico (n - 1 / 2 : α) (n + 1 / 2) := by
  norm_num [round_eq, floor_eq_iff, ← lt_sub_iff_add_lt, add_sub_assoc]

