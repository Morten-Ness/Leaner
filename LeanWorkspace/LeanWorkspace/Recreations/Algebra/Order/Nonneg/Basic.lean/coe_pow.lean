import Mathlib

variable {α : Type*}

variable [MonoidWithZero α] [Preorder α] [ZeroLEOneClass α] [PosMulMono α]

theorem coe_pow (a : { x : α // 0 ≤ x }) (n : ℕ) :
    (↑(a ^ n) : α) = (a : α) ^ n := rfl

