import Mathlib

variable {α : Type*}

theorem coe_add [AddZeroClass α] [Preorder α] [AddLeftMono α]
    (a b : { x : α // 0 ≤ x }) : ((a + b : { x : α // 0 ≤ x }) : α) = a + b := rfl

