import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

theorem midpoint_pointReflection_right (x y : P) :
    midpoint R y (Equiv.pointReflection x y) = x := midpoint_eq_iff.2 rfl

nonrec lemma AffineEquiv.midpoint_pointReflection_left (x y : P) :
    midpoint R (pointReflection R x y) y = x :=
  midpoint_pointReflection_left x y

nonrec lemma AffineEquiv.midpoint_pointReflection_right (x y : P) :
    midpoint R y (pointReflection R x y) = x :=
  midpoint_pointReflection_right x y

