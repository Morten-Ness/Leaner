import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

private theorem of_boolalg_symmDiff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b := calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [BooleanRing.mul_self, BooleanRing.add_self, add_zero]


theorem ofBoolRing_sub (a b : AsBoolRing α) : ofBoolRing (a - b) = ofBoolRing a ∆ ofBoolRing b := rfl

