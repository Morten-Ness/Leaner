import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem top_add (a : α) : ⊤ + a = ⊤ := LinearOrderedAddCommMonoidWithTop.top_add' a

