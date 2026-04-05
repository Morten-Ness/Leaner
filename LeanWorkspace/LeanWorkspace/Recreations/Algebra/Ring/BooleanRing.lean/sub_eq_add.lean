import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] (a b : α)

theorem sub_eq_add : a - b = a + b := by rw [sub_eq_add_neg, add_right_inj, BooleanRing.neg_eq]

