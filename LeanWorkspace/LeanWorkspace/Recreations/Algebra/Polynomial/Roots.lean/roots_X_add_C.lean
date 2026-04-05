import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_X_add_C (r : R) : Polynomial.roots (X + C r) = {-r} := by simpa using Polynomial.roots_X_sub_C (-r)

