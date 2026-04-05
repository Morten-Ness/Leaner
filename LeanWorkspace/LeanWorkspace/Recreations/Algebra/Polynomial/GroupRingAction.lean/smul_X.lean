import Mathlib

open scoped Polynomial

variable (M : Type*) [Monoid M]

variable (R : Type*) [Semiring R]

variable [MulSemiringAction M R]

theorem smul_X (m : M) : (m • Polynomial.X : R[X]) = Polynomial.X := (Polynomial.smul_eq_map R m).symm ▸ map_X _

