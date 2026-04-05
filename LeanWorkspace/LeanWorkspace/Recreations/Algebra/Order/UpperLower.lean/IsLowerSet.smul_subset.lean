import Mathlib

variable {α : Type*} [CommMonoid α] [Preorder α] [IsOrderedMonoid α] {s : Set α} {x : α}

theorem IsLowerSet.smul_subset (hs : IsLowerSet s) (hx : x ≤ 1) : x • s ⊆ s := smul_set_subset_iff.2 fun _ ↦ hs <| mul_le_of_le_one_left' hx

