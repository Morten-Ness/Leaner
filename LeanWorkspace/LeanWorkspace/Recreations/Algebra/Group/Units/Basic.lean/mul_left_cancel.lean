import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c := IsUnit.mul_right_inj h.1

