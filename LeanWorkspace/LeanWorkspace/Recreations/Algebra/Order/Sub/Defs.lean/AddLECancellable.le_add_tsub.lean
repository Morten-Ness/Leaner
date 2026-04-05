import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem le_add_tsub (hb : AddLECancellable b) : a ≤ a + b - b := by
  rw [add_comm]
  exact AddLECancellable.le_add_tsub_swap hb

