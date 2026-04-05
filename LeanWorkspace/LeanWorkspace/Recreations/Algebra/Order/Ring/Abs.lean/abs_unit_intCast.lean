import Mathlib

variable {α : Type*}

variable [CommRing α] [LinearOrder α] (a b : α) (n : ℕ)

theorem abs_unit_intCast [IsOrderedRing α] (a : ℤˣ) : |((a : ℤ) : α)| = 1 := by
  cases Int.units_eq_one_or a <;> simp_all

