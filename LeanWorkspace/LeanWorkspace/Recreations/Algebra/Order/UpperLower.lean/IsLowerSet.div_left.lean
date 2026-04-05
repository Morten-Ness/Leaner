import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsLowerSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  {s t : Set α} (ht : IsLowerSet t) : IsUpperSet (s / t) := ht.toDual.div_left

