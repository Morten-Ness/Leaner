import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [CommGroup α] [MulLeftMono α]

theorem mabs_mul_le (a b : α) : |a * b|ₘ ≤ |a|ₘ * |b|ₘ := by
  apply sup_le
  · exact mul_le_mul' (le_mabs_self a) (le_mabs_self b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_mabs _) (inv_le_mabs _)

