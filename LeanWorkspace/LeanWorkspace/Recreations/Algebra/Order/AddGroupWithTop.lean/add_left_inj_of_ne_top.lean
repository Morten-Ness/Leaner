import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_left_inj_of_ne_top (h : a ≠ ⊤) : b + a = c + a ↔ b = c := (add_left_injective_of_ne_top _ h).eq_iff

