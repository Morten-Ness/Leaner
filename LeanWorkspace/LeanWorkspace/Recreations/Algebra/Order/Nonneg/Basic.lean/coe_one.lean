import Mathlib

variable {α : Type*}

variable [Zero α] [One α] [LE α] [ZeroLEOneClass α]

theorem coe_one : ((1 : { x : α // 0 ≤ x }) : α) = 1 := rfl

