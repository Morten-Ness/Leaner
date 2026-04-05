import Mathlib

variable {α : Type*} [Preorder α] [OrderBot α] [AddMonoidWithOne α] [SuccAddOrder α]

theorem one_le_iff_pos {α : Type*} [PartialOrder α] [AddMonoidWithOne α]
    [ZeroLEOneClass α] [NeZero (1 : α)] [SuccAddOrder α] (a : WithBot α) : 1 ≤ a ↔ 0 < a := by
  cases a <;> simp [Order.one_le_iff_pos]

