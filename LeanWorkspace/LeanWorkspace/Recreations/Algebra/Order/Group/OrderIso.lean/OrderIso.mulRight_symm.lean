import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulRightMono α] {a : α}

theorem OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ := by
  ext x
  rfl

