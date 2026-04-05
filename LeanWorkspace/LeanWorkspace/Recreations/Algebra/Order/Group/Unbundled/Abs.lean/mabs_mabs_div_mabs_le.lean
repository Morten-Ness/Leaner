import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [CommGroup α] [MulLeftMono α]

theorem mabs_mabs_div_mabs_le (a b : α) : |(|a|ₘ / |b|ₘ)|ₘ ≤ |a / b|ₘ := by
  rw [mabs, sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert mabs_mul_le (a / b) b
    rw [div_mul_cancel]
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, mabs_div_comm]
    convert mabs_mul_le (b / a) a
    · rw [div_mul_cancel]

