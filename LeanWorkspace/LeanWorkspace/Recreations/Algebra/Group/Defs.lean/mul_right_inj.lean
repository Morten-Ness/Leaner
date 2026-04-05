import Mathlib

variable {G : Type*}

variable [Mul G]

variable [IsLeftCancelMul G] {a b c : G}

theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c := (mul_right_injective a).eq_iff

