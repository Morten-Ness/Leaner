import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem add_neg_cancel_iff_ne_top : a + -a = 0 ↔ a ≠ ⊤ where
  mp := by contrapose; simp +contextual
  mpr h := add_neg_cancel_of_ne_top h

