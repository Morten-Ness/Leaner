import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

omit [IsOrderedMonoid α] in
theorem Ici_one : Ici (1 : α) = 1 := rfl

