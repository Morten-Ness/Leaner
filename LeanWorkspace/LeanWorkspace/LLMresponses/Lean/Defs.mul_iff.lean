import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} :
    IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y := by
  simpa using isUnit_mul_iff x y
