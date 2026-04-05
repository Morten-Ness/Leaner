import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_inj : p.mirror = q.mirror ↔ p = q := Polynomial.mirror_involutive.injective.eq_iff

