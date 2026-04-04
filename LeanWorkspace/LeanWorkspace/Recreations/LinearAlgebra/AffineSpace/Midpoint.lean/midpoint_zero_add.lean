import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

variable (R)

theorem midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y := (midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 <| by simp

