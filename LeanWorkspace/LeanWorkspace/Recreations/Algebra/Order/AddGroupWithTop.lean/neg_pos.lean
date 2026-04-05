import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem neg_pos : 0 < -a ↔ a < 0 ∨ a = ⊤ := by
  simpa using LinearOrderedAddCommGroupWithTop.sub_pos (a := 0) (b := a)

