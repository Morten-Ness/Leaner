import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsRightCancelMul G] {a b c : G}

theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c := (mul_left_injective a).eq_iff

