import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [CommGroup α] [MulLeftMono α]

theorem mabs_div_eq_leOnePart_sq (a : α) : |a|ₘ / a = a⁻ᵐ ^ 2 := by
  rw [sq, ← mul_div_div_cancel, oneLePart_mul_leOnePart, oneLePart_div_leOnePart]

