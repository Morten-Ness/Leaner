import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

variable (R)

theorem midpoint_self_neg (x : V) : midpoint R x (-x) = 0 := by
  rw [midpoint_eq_smul_add, add_neg_cancel, smul_zero]

