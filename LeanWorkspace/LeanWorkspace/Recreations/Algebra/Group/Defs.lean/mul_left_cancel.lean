import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsLeftCancelMul G] {a b c : G}

theorem mul_left_cancel : a * b = a * c → b = c := (IsLeftCancelMul.mul_left_cancel a ·)

