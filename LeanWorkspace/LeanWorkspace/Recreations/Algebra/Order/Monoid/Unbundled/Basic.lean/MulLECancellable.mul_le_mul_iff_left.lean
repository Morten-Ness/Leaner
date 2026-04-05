import Mathlib

variable {α β : Type*}

variable [LE α]

theorem mul_le_mul_iff_left [Mul α] [MulLeftMono α] {a b c : α}
    (ha : MulLECancellable a) : a * b ≤ a * c ↔ b ≤ c := ⟨fun h => ha h, fun h => mul_le_mul_right h a⟩

