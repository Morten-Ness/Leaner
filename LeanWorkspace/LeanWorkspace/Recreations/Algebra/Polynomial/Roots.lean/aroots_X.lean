import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_X [CommRing S] [IsDomain S] [Algebra T S] :
    aroots (X : T[X]) S = {0} := by
  rw [Polynomial.aroots_def, map_X, Polynomial.roots_X]

