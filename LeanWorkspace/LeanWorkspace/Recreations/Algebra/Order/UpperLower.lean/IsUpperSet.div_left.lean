import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsUpperSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
    {s t : Set α} (ht : IsUpperSet t) : IsLowerSet (s / t) := by
  rw [div_eq_mul_inv]
  exact ht.inv.mul_left

