import Mathlib

variable {α : Type*}

variable {α : Type*} [Monoid α]

variable [Preorder α] [CanonicallyOrderedMul α] [MulRightMono α]

omit [MulRightMono α] in
theorem Ici_one_eq_univ : Set.Ici (1 : α) = Set.univ := by aesop

