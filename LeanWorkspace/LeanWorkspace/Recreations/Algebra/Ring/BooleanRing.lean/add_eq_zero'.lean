import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] (a b : α)

theorem add_eq_zero' : a + b = 0 ↔ a = b := calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [BooleanRing.neg_eq]

