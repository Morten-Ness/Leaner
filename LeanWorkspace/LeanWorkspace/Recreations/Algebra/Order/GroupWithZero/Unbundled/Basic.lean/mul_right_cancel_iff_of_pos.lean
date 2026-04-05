import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [PartialOrder α]

theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c := ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

