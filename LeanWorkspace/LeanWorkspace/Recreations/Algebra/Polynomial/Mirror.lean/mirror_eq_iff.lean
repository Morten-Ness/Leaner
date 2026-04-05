import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror := Polynomial.mirror_involutive.eq_iff

