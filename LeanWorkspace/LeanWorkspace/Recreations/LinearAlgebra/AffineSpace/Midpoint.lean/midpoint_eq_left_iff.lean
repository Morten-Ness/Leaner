import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

variable (R)

theorem midpoint_eq_left_iff {x y : P} : midpoint R x y = x ↔ x = y := by
  rw [midpoint_eq_iff, pointReflection_self]

