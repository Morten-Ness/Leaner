import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

omit [IsOrderedMonoid α] in
theorem coe_one : ((1 : UpperSet α) : Set α) = Set.Ici 1 := rfl

