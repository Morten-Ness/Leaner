import Mathlib

open scoped Ring

variable {α : Type u}

variable [MonoidWithZero α]

theorem Ring.inverse_invertible (x : α) [Invertible x] : x⁻¹ʳ = ⅟x := Ring.inverse_unit (unitOfInvertible _)

