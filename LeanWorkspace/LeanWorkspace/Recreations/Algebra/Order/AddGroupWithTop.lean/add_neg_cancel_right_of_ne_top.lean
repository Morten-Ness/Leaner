import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem add_neg_cancel_right_of_ne_top (hb : b ≠ ⊤) (a : α) : a + b + -b = a := by
  simp [add_assoc, add_neg_cancel_of_ne_top hb]

