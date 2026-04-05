import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_C (a : R) : (C a).mirror = C a := Polynomial.mirror_monomial 0 a

