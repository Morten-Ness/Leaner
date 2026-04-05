import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : ℕ) :
    (p ^ n).aroots S = n • p.aroots S := by
  rw [Polynomial.aroots_def, Polynomial.map_pow, Polynomial.roots_pow]

