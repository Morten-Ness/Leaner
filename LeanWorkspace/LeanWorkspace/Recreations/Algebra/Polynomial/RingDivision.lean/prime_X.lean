import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem prime_X : Prime (Polynomial.X : R[X]) := by
  convert Polynomial.prime_X_sub_C (0 : R)
  simp

