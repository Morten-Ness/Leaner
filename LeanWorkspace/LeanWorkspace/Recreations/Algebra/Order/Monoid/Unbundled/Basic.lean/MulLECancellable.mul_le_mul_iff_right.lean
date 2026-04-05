import Mathlib

variable {α β : Type*}

variable [LE α]

theorem mul_le_mul_iff_right [Mul α] [i : @Std.Commutative α (· * ·)]
    [MulLeftMono α] {a b c : α} (ha : MulLECancellable a) :
    b * a ≤ c * a ↔ b ≤ c := by rw [i.comm b, i.comm c, MulLECancellable.mul_le_mul_iff_left ha]

