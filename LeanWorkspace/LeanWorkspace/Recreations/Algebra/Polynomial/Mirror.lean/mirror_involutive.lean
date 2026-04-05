import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_involutive : Function.Involutive (Polynomial.mirror : R[X] → R[X]) := Polynomial.mirror_mirror

