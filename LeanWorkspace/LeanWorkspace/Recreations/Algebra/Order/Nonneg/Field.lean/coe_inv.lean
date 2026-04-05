import Mathlib

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

theorem coe_inv (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = (a : α)⁻¹ := rfl

