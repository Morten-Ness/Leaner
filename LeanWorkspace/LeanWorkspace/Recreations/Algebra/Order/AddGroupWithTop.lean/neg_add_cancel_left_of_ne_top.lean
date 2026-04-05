import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem neg_add_cancel_left_of_ne_top (ha : a ≠ ⊤) (b : α) : -a + (a + b) = b := by
  simp [← add_assoc, LinearOrderedAddCommGroupWithTop.neg_add_cancel_of_ne_top ha]

