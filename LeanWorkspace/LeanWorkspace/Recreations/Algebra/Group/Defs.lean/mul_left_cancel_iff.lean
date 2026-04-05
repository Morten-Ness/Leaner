import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsLeftCancelMul G] {a b c : G}

theorem mul_left_cancel_iff : a * b = a * c ↔ b = c := ⟨mul_left_cancel, congrArg _⟩

