import Mathlib

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

theorem coe_div (a b : { x : α // 0 ≤ x }) : ((a / b : { x : α // 0 ≤ x }) : α) = a / b := rfl

