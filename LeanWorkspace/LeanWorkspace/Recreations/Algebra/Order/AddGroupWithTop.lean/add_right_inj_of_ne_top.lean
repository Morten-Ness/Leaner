import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_right_inj_of_ne_top (h : a ≠ ⊤) : a + b = a + c ↔ b = c := (add_right_injective_of_ne_top _ h).eq_iff

