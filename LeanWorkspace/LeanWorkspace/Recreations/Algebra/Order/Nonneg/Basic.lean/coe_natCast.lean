import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

theorem coe_natCast (n : ℕ) : ((↑n : { x : α // 0 ≤ x }) : α) = n := rfl

