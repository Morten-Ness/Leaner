import Mathlib

variable {α : Type u}

variable [Group α] [LE α]

variable [MulLeftMono α]

theorem OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ := by
  ext x
  rfl

