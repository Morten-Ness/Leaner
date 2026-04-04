import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

theorem midpoint_pointReflection_left (x y : P) :
    midpoint R (Equiv.pointReflection x y) y = x := midpoint_eq_iff.2 <| Equiv.pointReflection_involutive _ _

