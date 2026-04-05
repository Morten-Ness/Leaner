import Mathlib

variable {α : Type*} [CommMonoid α] [Preorder α] [IsOrderedMonoid α] {s : Set α} {x : α}

theorem IsUpperSet.smul_subset (hs : IsUpperSet s) (hx : 1 ≤ x) : x • s ⊆ s := smul_set_subset_iff.2 fun _ ↦ hs <| le_mul_of_one_le_left' hx

