import Mathlib

variable {α : Type*}

variable [MulZeroClass α] [Preorder α] [PosMulMono α]

theorem coe_mul (a b : { x : α // 0 ≤ x }) :
    ((a * b : { x : α // 0 ≤ x }) : α) = a * b := rfl

