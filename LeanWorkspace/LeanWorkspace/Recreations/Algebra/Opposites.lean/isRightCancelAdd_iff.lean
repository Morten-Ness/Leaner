import Mathlib

variable {α β : Type*}

theorem isRightCancelAdd_iff [Add α] : IsRightCancelAdd αᵐᵒᵖ ↔ IsRightCancelAdd α where
  mp _ := ⟨fun _ _ _ eq ↦ MulOpposite.op_injective <| add_right_cancel (congr_arg MulOpposite.op eq)⟩
  mpr _ := inferInstance

