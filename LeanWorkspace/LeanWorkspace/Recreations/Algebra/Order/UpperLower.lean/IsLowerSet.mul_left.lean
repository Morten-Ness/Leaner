import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSet (s * t) := ht.toDual.mul_left

