import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsRightCancelMul G] {a b c : G}

theorem mul_left_injective (a : G) : Function.Injective (· * a) := fun _ _ ↦ mul_right_cancel

