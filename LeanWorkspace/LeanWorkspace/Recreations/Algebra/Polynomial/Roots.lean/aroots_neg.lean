import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_neg [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) :
    (-p).aroots S = p.aroots S := by
  rw [aroots, Polynomial.map_neg, Polynomial.roots_neg]

