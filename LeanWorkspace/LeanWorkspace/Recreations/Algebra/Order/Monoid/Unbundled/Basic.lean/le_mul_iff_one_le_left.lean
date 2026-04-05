import Mathlib

variable {α β : Type*}

variable [LE α]

theorem le_mul_iff_one_le_left [MulOneClass α] [i : @Std.Commutative α (· * ·)]
    [MulLeftMono α] {a b : α} (ha : MulLECancellable a) :
    a ≤ b * a ↔ 1 ≤ b := by rw [i.comm, MulLECancellable.le_mul_iff_one_le_right ha]

