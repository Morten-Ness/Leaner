import Mathlib

variable {α : Type*}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

theorem inv_uIcc (a b : α) : [[a, b]]⁻¹ = [[a⁻¹, b⁻¹]] := by
  simp only [uIcc, Set.inv_Icc, inv_sup, inv_inf]

