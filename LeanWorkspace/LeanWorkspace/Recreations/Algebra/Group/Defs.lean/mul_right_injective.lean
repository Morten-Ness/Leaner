import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsLeftCancelMul G] {a b c : G}

theorem mul_right_injective (a : G) : Function.Injective (a * ·) := fun _ _ ↦ mul_left_cancel

