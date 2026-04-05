import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsRightCancelMul G] {a b c : G}

theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c := (mul_left_injective a).ne_iff

