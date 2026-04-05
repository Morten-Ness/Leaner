import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_left_injective_of_ne_top (h : b ≠ ⊤) : Function.Injective fun x ↦ x - b := by
  simpa [sub_eq_add_neg] using add_left_injective_of_ne_top (-b) (by simpa)

