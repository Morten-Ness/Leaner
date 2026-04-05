import Mathlib

variable {α β : Type*}

theorem isCancelAdd_iff [Add α] : IsCancelAdd αᵐᵒᵖ ↔ IsCancelAdd α := by
  simp_rw [isCancelAdd_iff, MulOpposite.isLeftCancelAdd_iff, MulOpposite.isRightCancelAdd_iff]

