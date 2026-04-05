import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_right_inj_of_ne_top (h : a ≠ ⊤) : a - b = a - c ↔ b = c := (LinearOrderedAddCommGroupWithTop.sub_right_injective_of_ne_top h).eq_iff

