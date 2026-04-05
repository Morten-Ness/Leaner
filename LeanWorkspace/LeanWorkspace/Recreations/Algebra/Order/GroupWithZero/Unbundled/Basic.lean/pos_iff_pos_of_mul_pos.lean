import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b := ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

