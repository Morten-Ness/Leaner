import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_le_sub_iff_left_of_ne_top (h : a ≠ ⊤) : b - a ≤ c - a ↔ b ≤ c := (LinearOrderedAddCommGroupWithTop.sub_left_strictMono_of_ne_top h).le_iff_le

