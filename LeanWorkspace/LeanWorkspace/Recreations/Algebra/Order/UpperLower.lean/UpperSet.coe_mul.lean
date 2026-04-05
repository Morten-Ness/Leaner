import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * t := rfl

