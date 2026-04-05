import Mathlib

variable {α : Type u}

variable [Group α] [LinearOrder α]

variable [MulLeftMono α]

variable {a b : α}

theorem div_le_div_flip {α : Type*} [CommGroup α] [LinearOrder α]
    [MulLeftMono α] {a b : α} : a / b ≤ b / a ↔ a ≤ b := by
  rw [div_eq_mul_inv b, mul_comm]
  exact div_le_inv_mul_iff

