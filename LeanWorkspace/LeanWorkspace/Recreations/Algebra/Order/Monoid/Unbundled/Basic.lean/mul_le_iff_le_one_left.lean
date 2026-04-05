import Mathlib

variable {α β : Type*}

variable [LE α]

theorem mul_le_iff_le_one_left [MulOneClass α] [i : @Std.Commutative α (· * ·)]
    [MulLeftMono α] {a b : α} (ha : MulLECancellable a) :
    b * a ≤ a ↔ b ≤ 1 := by rw [i.comm, MulLECancellable.mul_le_iff_le_one_right ha]

