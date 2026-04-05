import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_eq_zero (ha : a ≠ ⊤) : b - a = 0 ↔ b = a := by
  rw [← sub_self_eq_zero_of_ne_top ha, LinearOrderedAddCommGroupWithTop.sub_left_inj_of_ne_top ha]

