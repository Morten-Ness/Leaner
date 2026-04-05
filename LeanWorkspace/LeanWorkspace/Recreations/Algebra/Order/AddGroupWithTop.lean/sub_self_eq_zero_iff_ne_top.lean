import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_self_eq_zero_iff_ne_top : a - a = 0 ↔ a ≠ ⊤ := by
  rw [sub_eq_add_neg, LinearOrderedAddCommGroupWithTop.add_neg_cancel_iff_ne_top]

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

