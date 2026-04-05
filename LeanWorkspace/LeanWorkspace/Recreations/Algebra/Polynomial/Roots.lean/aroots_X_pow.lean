import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : ℕ) :
    (X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [Polynomial.aroots_pow, Polynomial.aroots_X]

