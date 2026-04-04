import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

variable (R)

theorem midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y) = x := by
  rw [sub_eq_add_neg, ← vadd_eq_add, ← vadd_eq_add, ← midpoint_vadd_midpoint]; simp

