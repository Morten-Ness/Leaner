import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

theorem Equiv.pointReflection_midpoint_right (x y : P) :
    (Equiv.pointReflection (midpoint R x y)) y = x := by
  rw [midpoint_comm, Equiv.pointReflection_midpoint_left]

