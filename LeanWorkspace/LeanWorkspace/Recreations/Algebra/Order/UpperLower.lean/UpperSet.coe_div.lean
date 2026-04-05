import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem coe_div (s t : UpperSet α) : (↑(s / t) : Set α) = s / t := rfl

