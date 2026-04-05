import Mathlib

variable {α β G M : Type*}

variable [DivInvMonoid G]

theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c := (mul_div_assoc _ _ _).symm

