import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) :
    Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R) := by
  rw [Polynomial.roots_C_mul _ ha, Polynomial.roots_X_pow]

