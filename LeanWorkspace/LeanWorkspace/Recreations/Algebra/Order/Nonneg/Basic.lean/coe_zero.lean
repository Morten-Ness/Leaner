import Mathlib

variable {α : Type*}

theorem coe_zero [Zero α] [Preorder α] : ((0 : { x : α // 0 ≤ x }) : α) = 0 := rfl

