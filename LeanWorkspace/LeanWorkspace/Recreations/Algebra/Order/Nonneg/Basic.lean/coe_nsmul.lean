import Mathlib

variable {α : Type*}

theorem coe_nsmul [AddMonoid α] [Preorder α] [AddLeftMono α]
    (n : ℕ) (a : { x : α // 0 ≤ x }) : ((n • a : { x : α // 0 ≤ x }) : α) = n • (a : α) := rfl

