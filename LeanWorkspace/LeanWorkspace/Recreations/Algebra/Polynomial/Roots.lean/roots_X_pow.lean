import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [Polynomial.roots_pow, Polynomial.roots_X]

