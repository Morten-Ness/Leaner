import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_X : X.mirror = (X : R[X]) := Polynomial.mirror_monomial 1 (1 : R)

