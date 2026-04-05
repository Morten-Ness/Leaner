import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsRightCancelMul G] {a b c : G}

theorem mul_right_cancel : a * b = c * b → a = c := (IsRightCancelMul.mul_right_cancel b ·)

