import Mathlib

variable {α β : Type*}

theorem isLeftCancelAdd_iff [Add α] : IsLeftCancelAdd αᵐᵒᵖ ↔ IsLeftCancelAdd α where
  mp _ := ⟨fun _ _ _ eq ↦ MulOpposite.op_injective <| add_left_cancel (congr_arg MulOpposite.op eq)⟩
  mpr _ := inferInstance

