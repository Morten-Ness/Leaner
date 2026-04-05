import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpperSet (s * t) := by
  rw [mul_comm]
  exact hs.mul_left

