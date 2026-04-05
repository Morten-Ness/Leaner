import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c := IsUnit.mul_left_inj h.1

