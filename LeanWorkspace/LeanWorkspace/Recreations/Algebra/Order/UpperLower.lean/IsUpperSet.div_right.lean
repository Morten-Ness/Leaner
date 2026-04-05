import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsUpperSet.div_right (hs : IsUpperSet s) : IsUpperSet (s / t) := by
  rw [div_eq_mul_inv]
  exact hs.mul_right

