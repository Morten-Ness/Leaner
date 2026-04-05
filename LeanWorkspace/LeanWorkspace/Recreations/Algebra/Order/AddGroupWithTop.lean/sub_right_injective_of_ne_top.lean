import Mathlib

variable {G α : Type*}

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

theorem sub_right_injective_of_ne_top (h : b ≠ ⊤) : Function.Injective fun x ↦ b - x := by
  simpa [sub_eq_add_neg] using (add_right_injective_of_ne_top b h).comp neg_injective

