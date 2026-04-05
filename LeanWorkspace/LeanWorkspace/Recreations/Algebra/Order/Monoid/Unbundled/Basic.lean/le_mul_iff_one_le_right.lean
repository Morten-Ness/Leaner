import Mathlib

variable {α β : Type*}

variable [LE α]

theorem le_mul_iff_one_le_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a ≤ a * b ↔ 1 ≤ b := Iff.trans (by rw [mul_one]) MulLECancellable.mul_le_mul_iff_left ha

