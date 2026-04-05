import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

private theorem of_boolalg_symmDiff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b := calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [BooleanRing.mul_self, BooleanRing.add_self, add_zero]


theorem ofBoolRing_symm_eq : (@ofBoolRing α).symm = toBoolRing := rfl

