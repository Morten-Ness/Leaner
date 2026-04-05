import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] (a b : α)

theorem neg_eq : -a = a := calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [BooleanRing.add_self, zero_add]

