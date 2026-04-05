import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_le_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c := (add_right_strictMono_of_ne_top h).le_iff_le

