import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s) := hs.image <| OrderIso.mulLeft _

