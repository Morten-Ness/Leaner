import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

variable (R)

theorem midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ Equiv.pointReflection z x = y := midpoint_eq_iff

