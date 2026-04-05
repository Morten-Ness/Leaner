import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem Set.OrdConnected.smul (hs : s.OrdConnected) : (a • s).OrdConnected := by
  rw [← hs.upperClosure_inter_lowerClosure, smul_set_inter]
  exact (upperClosure _).upper.smul.ordConnected.inter (lowerClosure _).lower.smul.ordConnected

