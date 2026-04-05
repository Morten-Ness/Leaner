import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) ≤ a - b + c := tsub_le_iff_right.2 <|
    calc
      a ≤ a - b + b := le_tsub_add
      _ ≤ a - b + (c + (b - c)) := by grw [← le_add_tsub]
      _ = a - b + c + (b - c) := (add_assoc _ _ _).symm

