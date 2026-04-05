import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem neg_add_cancel_of_ne_top (ha : a ≠ ⊤) : -a + a = 0 := by
  simp [add_comm, add_neg_cancel_of_ne_top ha]

