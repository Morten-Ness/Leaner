import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem isUnit_resolvent {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (resolvent a r) := isUnit_ringInverse.symm

