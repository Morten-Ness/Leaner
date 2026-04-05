import Mathlib

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

theorem coe_zpow (a : { x : α // 0 ≤ x }) (n : ℤ) :
    ((a ^ n : { x : α // 0 ≤ x }) : α) = (a : α) ^ n := rfl

