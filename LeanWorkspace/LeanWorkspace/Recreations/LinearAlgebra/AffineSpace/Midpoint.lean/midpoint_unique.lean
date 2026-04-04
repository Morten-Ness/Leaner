import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

variable (R)

theorem midpoint_unique (R' : Type*) [Ring R'] [Invertible (2 : R')] [Module R' V] (x y : P) :
    midpoint R x y = midpoint R' x y := (midpoint_eq_iff' R).2 <| (midpoint_eq_iff' R').1 rfl

