import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s) := hs.image <| OrderIso.mulLeft _

