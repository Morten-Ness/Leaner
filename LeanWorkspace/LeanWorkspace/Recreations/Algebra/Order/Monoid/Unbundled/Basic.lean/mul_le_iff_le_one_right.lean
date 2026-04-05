import Mathlib

variable {α β : Type*}

variable [LE α]

theorem mul_le_iff_le_one_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a * b ≤ a ↔ b ≤ 1 := Iff.trans (by rw [mul_one]) MulLECancellable.mul_le_mul_iff_left ha

