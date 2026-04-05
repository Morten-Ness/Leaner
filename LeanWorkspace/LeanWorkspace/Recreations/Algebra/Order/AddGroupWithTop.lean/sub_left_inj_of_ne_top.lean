import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_left_inj_of_ne_top (h : a ≠ ⊤) : b - a = c - a ↔ b = c := (LinearOrderedAddCommGroupWithTop.sub_left_injective_of_ne_top h).eq_iff

