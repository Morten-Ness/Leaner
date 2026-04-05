import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsRightCancelMul G] {a b c : G}

theorem mul_right_cancel_iff : b * a = c * a ↔ b = c := ⟨mul_right_cancel, congrArg (· * a)⟩

