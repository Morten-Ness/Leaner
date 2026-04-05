import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsUpperSet.inv {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  {s : Set α} (hs : IsUpperSet s) : IsLowerSet s⁻¹ := fun _ _ h ↦ hs <| inv_le_inv' h

