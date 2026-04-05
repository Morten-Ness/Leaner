import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_X : Polynomial.roots (X : R[X]) = {0} := by rw [← Polynomial.roots_X_sub_C, C_0, sub_zero]

