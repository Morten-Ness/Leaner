import Mathlib

variable {R : Type*} [Zero R]

theorem eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a := (eq_or_ne a 0).imp_right NeZero.mk

