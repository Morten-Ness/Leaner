import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

theorem add_top (a : α) : a + ⊤ = ⊤ := Trans.trans (add_comm _ _) (top_add _)

