import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_mirror : p.mirror.mirror = p := Polynomial.ext fun n => by
    rw [Polynomial.coeff_mirror, Polynomial.coeff_mirror, Polynomial.mirror_natDegree, Polynomial.mirror_natTrailingDegree, revAt_invol]

