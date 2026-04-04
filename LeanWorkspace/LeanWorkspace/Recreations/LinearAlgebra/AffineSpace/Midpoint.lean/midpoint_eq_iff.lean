import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

theorem midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ pointReflection R z x = y := eq_comm.trans
    ((injective_pointReflection_left_of_module R x).eq_iff'
        (AffineEquiv.pointReflection_midpoint_left x y)).symm

