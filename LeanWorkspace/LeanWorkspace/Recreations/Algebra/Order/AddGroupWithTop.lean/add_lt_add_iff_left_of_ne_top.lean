import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_lt_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a < c + a ↔ b < c := (add_left_strictMono_of_ne_top h).lt_iff_lt

