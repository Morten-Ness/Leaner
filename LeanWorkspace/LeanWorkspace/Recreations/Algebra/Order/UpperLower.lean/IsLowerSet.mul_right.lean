import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsLowerSet.mul_right (hs : IsLowerSet s) : IsLowerSet (s * t) := hs.toDual.mul_right

