import Mathlib

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

theorem IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSet (s * t) := by
  rw [← smul_eq_mul, ← Set.iUnion_smul_set]
  exact isUpperSet_iUnion₂ fun x _ ↦ ht.smul

