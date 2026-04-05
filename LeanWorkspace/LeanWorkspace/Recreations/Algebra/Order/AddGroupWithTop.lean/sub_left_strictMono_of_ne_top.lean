import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono fun x ↦ x - b := by
  simpa [sub_eq_add_neg] using add_left_strictMono_of_ne_top (b := -b) (by simpa)

