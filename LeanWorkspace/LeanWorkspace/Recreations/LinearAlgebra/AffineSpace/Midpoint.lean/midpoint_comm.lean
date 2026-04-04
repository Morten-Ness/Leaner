import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

theorem midpoint_comm (x y : P) : midpoint R x y = midpoint R y x := by
  rw [midpoint, ← lineMap_apply_one_sub, one_sub_invOf_two, midpoint]

